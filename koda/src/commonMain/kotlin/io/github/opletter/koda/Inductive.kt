package io.github.opletter.koda

context(env: Environment)
fun checkInductive(data: Inductive) {
    // (1): no duplicate universe parameters
    check(data.type.levelParams.toSet().size == data.type.levelParams.size) {
        "Duplicate universe parameters in $data"
    }

    val inductive = data.type
    val typeBinderCount = inductive.numParams + inductive.numIndices
    val inductiveParamTypes = mutableListOf<Expression>()
    val inductiveParamSortLevels = mutableListOf<Level>()

    // One pass over the inductive type telescope.
    val typeTailWhnf = walkForalls(
        expr = inductive.typeExpr,
        expectedBinders = typeBinderCount,
        owner = "Inductive type ${inductive.name}",
    ) { binderIndex, binderType, localCtx ->
        // Every binder domain in the type constructor must itself be a type.
        val binderSort = binderType.inferSort(localCtx = localCtx)
        if (binderIndex < inductive.numParams) {
            inductiveParamTypes += binderType
            inductiveParamSortLevels += binderSort
        }
    }

    val typeSort = typeTailWhnf as? Expression.Sort
        ?: error("Inductive type must reduce to Sort after $typeBinderCount binders, got ${typeTailWhnf.toStringDetailed()}")
    val inductiveSortLevel = typeSort.level
    val isInductiveProp = inductiveSortLevel.isLessOrEqual(Level.Zero)
    val maxFieldSortLevel = (listOf(inductiveSortLevel) + inductiveParamSortLevels).reduce { acc, level ->
        env.addCustomLevel { Level.Max(listOf(acc.il, level.il), it) }
    }

    data.registerInto(env)
    env.declTypeByName[data.type.name] = data.type.typeExpr
    val inductiveName = inductive.name as? Name.Str
        ?: error("Inductive name must be a string name, got ${inductive.name}")

    data.ctors.forEach { constructor ->
        // Basic declaration-level consistency.
//        check(constructor.inductName == inductive.name) {
//            "Constructor ${constructor.name} has wrong inductive target: expected ${inductive.name}, got ${constructor.inductName}"
//        }
//        check(constructor.numParams == inductive.numParams) {
//            "Constructor ${constructor.name} has wrong numParams: expected ${inductive.numParams}, got ${constructor.numParams}"
//        }
//        check(constructor.levelParams.toSet().size == constructor.levelParams.size) {
//            "Duplicate universe parameters in constructor $constructor"
//        }

        val ctorBinderCount = constructor.numParams + constructor.numFields
        val ctorTailExpr = walkForalls(
            expr = constructor.typeExpr,
            expectedBinders = ctorBinderCount,
            owner = "Constructor ${constructor.name}",
            reduceExpr = false,
        ) { binderIndex, binderType, localCtx ->
            if (binderIndex < constructor.numParams) {
                // Parameter section must exactly match the inductive parameters.
                val expectedParamType = inductiveParamTypes.getOrNull(binderIndex)
                    ?: error("Missing expected parameter type #$binderIndex for constructor ${constructor.name}")
                check(binderType.isDefEq(expectedParamType, localCtx, localCtx)) {
                    "Constructor ${constructor.name} parameter #$binderIndex type mismatch: expected ${expectedParamType.toStringDetailed()}, got ${binderType.toStringDetailed()}"
                }
            } else {
                // Field domain must be a type and satisfy universe + positivity checks.
                val fieldSort = binderType.inferSort(localCtx = localCtx)
                check(isInductiveProp || fieldSort.isLessOrEqual(maxFieldSortLevel)) {
                    "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} has sort ${fieldSort.toStringDetailed()} above allowed sort ${maxFieldSortLevel.toStringDetailed()}"
                }
                check(!binderType.hasNegativeOccurrenceOf(inductive.name)) {
                    "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} contains a non-positive occurrence of inductive ${inductive.name}"
                }
            }
        }

//        check(ctorTailExpr !is Expression.ForallE) {
//            "Constructor ${constructor.name} has too many binders: expected $ctorBinderCount"
//        }

        // Constructor result must be an application of the inductive with valid args.
        val [resultHead, resultArgs] = ctorTailExpr.unfoldApp()
        val resultConst = resultHead as? Expression.Const
            ?: error("Constructor ${constructor.name} must end in application of inductive ${inductive.name}, got ${ctorTailExpr.toStringDetailed()}")

//        check(resultConst.name == inductive.name) {
//            "Constructor ${constructor.name} must return inductive ${inductive.name}, got ${resultConst.name}"
//        }
//        check(resultConst.levels.size == inductive.levelParams.size) {
//            "Constructor ${constructor.name} has wrong number of universe args in result: expected ${inductive.levelParams.size}, got ${resultConst.levels.size}"
//        }
        inductive.levelParams.indices.forEach { i ->
            check(resultConst.levels[i].isEqual(inductive.levelParams[i])) {
                "Constructor ${constructor.name} result has wrong universe arg #$i: expected ${inductive.levelParams[i].toStringDetailed()}, got ${resultConst.levels[i].toStringDetailed()}"
            }
        }

        val expectedResultArgs = inductive.numParams + inductive.numIndices
//        check(resultArgs.size == expectedResultArgs) {
//            "Constructor ${constructor.name} result has wrong arg count: expected $expectedResultArgs, got ${resultArgs.size}"
//        }

        // Parameter arguments must be exactly the constructor parameter binders in order.
        repeat(inductive.numParams) { paramIndex ->
            val expectedBvar = ctorBinderCount - 1 - paramIndex
            val actualArg = resultArgs[paramIndex]
            check(actualArg is Expression.Bvar && actualArg.bvar == expectedBvar) {
                "Constructor ${constructor.name} result parameter #$paramIndex must be bvar $expectedBvar, got ${actualArg.toStringDetailed()}"
            }
        }

        // Index arguments may not recursively mention the inductive being declared.
        resultArgs.drop(inductive.numParams).forEach { indexArg: Expression ->
            check(!indexArg.containsConst(inductive.name)) {
                "Constructor ${constructor.name} index argument contains inductive ${inductive.name}: ${indexArg.toStringDetailed()}"
            }
        }

        env.declTypeByName[constructor.name] = constructor.typeExpr
    }
    // TODO: yikes this is bad code
    val recNamedRecCount = data.recs.count { rec ->
        val recName = rec.name as? Name.Str
            ?: error("Recursor name must be a string name, got ${rec.name}")
        val recParent = env.names[recName.pre]
            ?: error("Recursor ${rec.name} has missing parent name index ${recName.pre}")
        check(recParent == inductiveName) {
            "Recursor ${rec.name} must be in namespace ${inductive.name}"
        }
        env.declTypeByName[rec.name] = rec.typeExpr
        recName.str == "rec"
    }
    check(recNamedRecCount == 1) {
        "Inductive ${inductive.name} must declare exactly one recursor named ${inductive.name}.rec, got $recNamedRecCount"
    }
    data.recs.forEach { recursor ->
        checkRecursorRules(recursor)
    }
}

context(env: Environment)
private fun walkForalls(
    expr: Expression,
    expectedBinders: Int,
    owner: String,
    reduceExpr: Boolean = true,
    onBinder: (binderIndex: Int, binderType: Expression, localCtx: List<Expression>) -> Unit,
): Expression {
    var currentExpr = expr
    var currentLocalCtx: List<Expression> = emptyList()

    repeat(expectedBinders) { binderIndex ->
        val current = if (reduceExpr) currentExpr.reduce() else currentExpr
        val forall = current as? Expression.ForallE
            ?: error("$owner has too few binders: expected $expectedBinders, got $binderIndex")

        onBinder(binderIndex, forall.typeExpr, currentLocalCtx)
        currentLocalCtx = listOf(forall.typeExpr) + currentLocalCtx
        currentExpr = forall.bodyExpr
    }

    return if (reduceExpr) currentExpr.reduce() else currentExpr
}

context(env: Environment)
private fun collectForallBinders(
    expr: Expression,
    expectedBinders: Int,
    owner: String,
    reduceExpr: Boolean = false,
): Pair<List<Expression.ForallE>, Expression> {
    val binders = mutableListOf<Expression.ForallE>()
    var currentExpr = expr
    repeat(expectedBinders) { binderIndex ->
        val current = if (reduceExpr) currentExpr.reduce() else currentExpr
        val forall = current as? Expression.ForallE
            ?: error("$owner has too few binders: expected $expectedBinders, got $binderIndex")
        binders += forall
        currentExpr = forall.bodyExpr
    }
    return binders to if (reduceExpr) currentExpr.reduce() else currentExpr
}

context(env: Environment)
fun Inductive.RecursorVal.getMajorBinder(): Expression.ForallE {
    var tailExpr = this.typeExpr
    repeat(this.numParams + this.numMotives + this.numMinors + this.numIndices) { binderIndex ->
        val forall = tailExpr as? Expression.ForallE
            ?: error("Recursor ${this.name} has too few binders before major premise: expected ${this.numParams + this.numMotives + this.numMinors + this.numIndices}, got $binderIndex")
        tailExpr = forall.bodyExpr
    }
    return tailExpr as? Expression.ForallE
        ?: error("Recursor ${this.name} is missing a major premise binder")
}

context(env: Environment)
fun Inductive.RecursorVal.getMajorInductName(): Name {
    val majorType = this.getMajorBinder().typeExpr
    val [majorTypeHead, _] = majorType.unfoldApp()
    val majorTypeConst = majorTypeHead as? Expression.Const
        ?: error("Recursor ${this.name} major premise type must be const-headed, got ${majorType.toStringDetailed()}")
    return majorTypeConst.name
}

context(env: Environment)
private fun checkRecursorRules(recursor: Inductive.RecursorVal) {
    val majorInductName = recursor.getMajorInductName()
    val majorInductNameIndex = env.nameIndices[majorInductName]
        ?: error("Major inductive name index for ${majorInductName.toStringDetailed()} not found")
    val majorInductive = env.declarations[majorInductNameIndex] as? Inductive.InductiveVal
        ?: error("Recursor ${recursor.name} major premise type ${majorInductName.toStringDetailed()} is not an inductive")
    check(majorInductive.numIndices == recursor.numIndices) {
        "Recursor ${recursor.name} has wrong numIndices for major inductive ${majorInductName.toStringDetailed()}: expected ${majorInductive.numIndices}, got ${recursor.numIndices}"
    }

    val seenCtorNames = mutableSetOf<Name>()
    recursor.rules.forEach { rule ->
        check(seenCtorNames.add(rule.ctorName)) {
            "Recursor ${recursor.name} has duplicate rules"
        }
        val constructor = env.constructorByName[rule.ctorName]
            ?: error("Recursor ${recursor.name} references unknown constructor ${rule.ctorName}")
        check(constructor.inductName == majorInductName) {
            "Recursor ${recursor.name} has rule for constructor ${constructor.name} outside major inductive ${majorInductName.toStringDetailed()}"
        }
        check(rule.nfields == constructor.numFields) {
            "Recursor rule for ${constructor.name} has wrong nfields: expected ${constructor.numFields}, got ${rule.nfields}"
        }
        checkRecursorRuleType(recursor, constructor, rule, majorInductive)
    }
}

context(env: Environment)
private fun checkRecursorRuleType(
    recursor: Inductive.RecursorVal,
    constructor: Inductive.ConstructorVal,
    rule: Inductive.RecursorVal.RecursorRule,
    majorInductive: Inductive.InductiveVal,
) {
    val prefixBinderCount = recursor.numParams + recursor.numMotives + recursor.numMinors
    val expectedRuleBinderCount = prefixBinderCount + constructor.numFields
    val inferredRuleType = rule.rhsExpr.inferType()
    val ruleTypeInfo = collectForallBinders(
        expr = inferredRuleType,
        expectedBinders = expectedRuleBinderCount,
        owner = "Recursor rule for ${constructor.name}",
    )
    val ruleBinders = ruleTypeInfo.first
    val ruleResultType = ruleTypeInfo.second

    val ruleLocalCtx =
        ruleBinders.fold(emptyList<Expression>()) { localCtx: List<Expression>, binder: Expression.ForallE ->
            listOf(binder.typeExpr) + localCtx
        }

    fun binderExpr(outerIndex: Int): Expression {
        return env.addCustomExpr {
            Expression.Bvar(ruleBinders.lastIndex - outerIndex, it)
        }
    }

    val prefixArgs = List(prefixBinderCount, ::binderExpr)
    val fieldArgs = List(constructor.numFields) { fieldIndex ->
        binderExpr(prefixBinderCount + fieldIndex)
    }

    val majorBinderType = recursor.getMajorBinder().typeExpr
    val [majorBinderTypeHead, majorBinderTypeArgs] = majorBinderType.unfoldApp()
    val majorBinderTypeConst = majorBinderTypeHead as? Expression.Const
        ?: error("Recursor ${recursor.name} major premise type must be const-headed, got ${majorBinderType.toStringDetailed()}")
    check(majorBinderTypeConst.name == majorInductive.name) {
        "Recursor ${recursor.name} major premise type mismatch: expected ${majorInductive.name}, got ${majorBinderTypeConst.name}"
    }
    check(majorBinderTypeArgs.size >= constructor.numParams) {
        "Recursor ${recursor.name} major premise type has too few args for constructor ${constructor.name}: expected at least ${constructor.numParams}, got ${majorBinderTypeArgs.size}"
    }
    val paramArgs = majorBinderTypeArgs.take(constructor.numParams).map { paramArg ->
        paramArg.dropOuterBinders(recursor.numIndices).lift(constructor.numFields)
    }

    val constructorNameIndex = env.nameIndices[constructor.name]
        ?: error("Constructor name index for ${constructor.name} not found")
    val constructorExpr = env.addCustomExpr {
        Expression.Const(_name = constructorNameIndex, us = majorBinderTypeConst.levels.map { it.il }, ie = it)
    }
    val majorExpr = constructorExpr.applyArgs(paramArgs + fieldArgs)
    val majorType = majorExpr.inferType(localCtx = ruleLocalCtx).reduce()
    val [majorTypeHead, majorTypeArgs] = majorType.unfoldApp()
    val majorTypeConst = majorTypeHead as? Expression.Const
        ?: error("Expected constructor result type for ${constructor.name}, got ${majorType.toStringDetailed()}")
    check(majorTypeConst.name == majorInductive.name) {
        "Constructor ${constructor.name} result type mismatch while checking ${recursor.name}: expected ${majorInductive.name}, got ${majorTypeConst.name}"
    }
    check(majorTypeArgs.size == constructor.numParams + majorInductive.numIndices) {
        "Constructor ${constructor.name} result has wrong arg count while checking ${recursor.name}: expected ${constructor.numParams + majorInductive.numIndices}, got ${majorTypeArgs.size}"
    }

    val recursorNameIndex = env.nameIndices[recursor.name]
        ?: error("Recursor name index for ${recursor.name} not found")
    val recursorExpr = env.addCustomExpr {
        Expression.Const(_name = recursorNameIndex, us = recursor.levelParams.map { it.il }, ie = it)
    }
    val expectedResultType = recursorExpr
        .applyArgs(prefixArgs + majorTypeArgs.drop(constructor.numParams) + listOf(majorExpr))
        .inferType(localCtx = ruleLocalCtx)
        .reduce()

    check(ruleResultType.isDefEq(expectedResultType, ruleLocalCtx, ruleLocalCtx)) {
        "Recursor rule for ${constructor.name} has wrong result type: expected ${expectedResultType.toStringDetailed()}, got ${ruleResultType.toStringDetailed()}"
    }
}

context(env: Environment)
private fun Expression.applyArgs(args: List<Expression>): Expression {
    if (args.isEmpty()) return this
    var result = this
    args.forEach { argExpr ->
        result = env.addCustomExpr { Expression.App(fn = result.ie, arg = argExpr.ie, ie = it) }
    }
    return result
}

context(env: Environment)
fun Expression.unfoldApp(): Pair<Expression, List<Expression>> {
    val args = mutableListOf<Expression>()
    var head = this
    while (head is Expression.App) {
        args += head.argExpr
        head = head.fnExpr
    }
    return head to args.asReversed()
}

context(env: Environment)
private fun Expression.containsConst(targetName: Name): Boolean {
    return when (this) {
        is Expression.App -> this.fnExpr.containsConst(targetName) || this.argExpr.containsConst(targetName)
        is Expression.Const -> this.name == targetName
        is Expression.ForallE -> this.typeExpr.containsConst(targetName) || this.bodyExpr.containsConst(targetName)
        is Expression.Lam -> this.typeExpr.containsConst(targetName) || this.bodyExpr.containsConst(targetName)
        is Expression.LetE ->
            this.typeExpr.containsConst(targetName) ||
                    this.valueExpr.containsConst(targetName) ||
                    this.bodyExpr.containsConst(targetName)

        is Expression.Bvar, is Expression.Mdata, is Expression.NatVal,
        is Expression.Proj, is Expression.Sort, is Expression.StrVal -> false
    }
}

context(env: Environment)
private fun Expression.hasNegativeOccurrenceOf(targetName: Name, polarity: Int = 1): Boolean {
    return when (this) {
        is Expression.App ->
            this.fnExpr.hasNegativeOccurrenceOf(targetName, polarity) ||
                    this.argExpr.hasNegativeOccurrenceOf(targetName, polarity)

        is Expression.Const -> this.name == targetName && polarity < 0

        is Expression.ForallE ->
            this.typeExpr.hasNegativeOccurrenceOf(targetName, -polarity) ||
                    this.bodyExpr.hasNegativeOccurrenceOf(targetName, polarity)

        is Expression.Lam ->
            this.typeExpr.hasNegativeOccurrenceOf(targetName, -polarity) ||
                    this.bodyExpr.hasNegativeOccurrenceOf(targetName, polarity)

        is Expression.LetE ->
            this.typeExpr.hasNegativeOccurrenceOf(targetName, polarity) ||
                    this.valueExpr.hasNegativeOccurrenceOf(targetName, polarity) ||
                    this.bodyExpr.hasNegativeOccurrenceOf(targetName, polarity)

        is Expression.Bvar, is Expression.Mdata, is Expression.NatVal,
        is Expression.Proj, is Expression.Sort, is Expression.StrVal -> false
    }
}