package io.github.opletter.koda

private data class InductiveTypeInfo(
    val paramTypes: List<Expression>,
    val paramSortLevels: List<Level>,
    val sortLevel: Level,
)

context(env: Environment)
fun checkInductive(data: Inductive) {
    check(data.types.isNotEmpty()) {
        "Inductive block must contain at least one type"
    }

    val inductives = data.types
    val blockNumParams = inductives.first().numParams
    val blockLevelParams = inductives.first().levelParams
    val blockNameIndices = inductives.map { inductive ->
        env.nameIndices[inductive.name]
            ?: error("Inductive name index for ${inductive.name.toStringDetailed()} not found")
    }
    val blockNames = inductives.map { it.name }
    val blockNameSet = blockNames.toSet()
    check(blockNames.size == blockNameSet.size) {
        "Inductive block has duplicate type names: ${blockNames.map { it.toStringDetailed() }}"
    }

    inductives.forEach { inductive ->
        // (1): no duplicate universe parameters
        check(inductive.hasDistinctLevelParams()) {
            "Duplicate universe parameters in $inductive"
        }
        check(inductive.numParams == blockNumParams) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong numParams: expected $blockNumParams, got ${inductive.numParams}"
        }
        check(inductive.all == blockNameIndices) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong all list: expected $blockNameIndices, got ${inductive.all}"
        }
        check(inductive.levelParams.isEqual(blockLevelParams)) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has mismatched universe parameters"
        }
    }

    val inductiveInfos = inductives.associateWith { analyzeInductiveType(it) }
    val firstInductive = inductives.first()
    val firstInfo = inductiveInfos[firstInductive]
        ?: error("Missing type info for ${firstInductive.name.toStringDetailed()}")
    inductives.drop(1).forEach { inductive ->
        val info = inductiveInfos[inductive] ?: error("Missing type info for ${inductive.name.toStringDetailed()}")
        checkSharedParams(firstInductive, firstInfo, inductive, info)
    }
    val fieldSortLevels: List<Level> =
        inductives.map { inductiveInfos.getValue(it).sortLevel } + firstInfo.paramSortLevels
    val maxFieldSortLevel = fieldSortLevels.reduce { acc: Level, level: Level ->
        makeLevelMax(acc, level)
    }

    data.registerInto(env)
    inductives.forEach { inductive ->
        env.declTypeByName[inductive.name] = inductive.typeExpr
    }

    val ctorsByInductive = data.ctors.groupBy { it.inductName }
    check(ctorsByInductive.keys.all { it in blockNameSet }) {
        "Mutual inductive block has constructor for an unrelated type: ${ctorsByInductive.keys.map { it.toStringDetailed() }}"
    }
    inductives.forEach { inductive ->
        val inductiveInfo = inductiveInfos[inductive]
            ?: error("Missing type info for ${inductive.name.toStringDetailed()}")
        val constructors = (ctorsByInductive[inductive.name] ?: emptyList()).sortedBy { it.cidx }
        check(constructors.size == inductive.ctors.size) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong constructor count: expected ${inductive.ctors.size}, got ${constructors.size}"
        }
        constructors.forEachIndexed { ctorIndex, constructor ->
            check(constructor.cidx == ctorIndex) {
                "Constructor ${constructor.name.toStringDetailed()} has wrong cidx: expected $ctorIndex, got ${constructor.cidx}"
            }
            val constructorNameIndex = env.nameIndices[constructor.name]
                ?: error("Constructor name index for ${constructor.name.toStringDetailed()} not found")
            check(inductive.ctors[ctorIndex] == constructorNameIndex) {
                "Mutual inductive ${inductive.name.toStringDetailed()} constructor list mismatch at #$ctorIndex"
            }
            checkConstructor(constructor, inductive, inductiveInfo, blockNameSet, maxFieldSortLevel)
            env.declTypeByName[constructor.name] = constructor.typeExpr
        }
    }
    check(data.ctors.size == inductives.sumOf { it.ctors.size }) {
        "Mutual inductive block has mismatched constructor inventory"
    }

    val recNamedRecCountByInductive = mutableMapOf<Name, Int>()
    data.recs.forEach { recursor ->
        check(recursor.all == blockNameIndices) {
            "Recursor ${recursor.name.toStringDetailed()} has wrong all list: expected $blockNameIndices, got ${recursor.all}"
        }
        check(recursor.numParams == blockNumParams) {
            "Recursor ${recursor.name.toStringDetailed()} has wrong numParams: expected $blockNumParams, got ${recursor.numParams}"
        }

        val recName = recursor.name as? Name.Str
            ?: error("Recursor name must be a string name, got ${recursor.name}")
        val recParent = env.names[recName.pre]
            ?: error("Recursor ${recursor.name} has missing parent name index ${recName.pre}")
        check(recParent in blockNameSet) {
            "Recursor ${recursor.name.toStringDetailed()} must be in one of the mutual inductive namespaces ${blockNames.map { it.toStringDetailed() }}"
        }
        if (recName.str == "rec") {
            recNamedRecCountByInductive[recParent] = recNamedRecCountByInductive.getOrElse(recParent, { 0 }) + 1
        }
        env.declTypeByName[recursor.name] = recursor.typeExpr
    }
    inductives.forEach { inductive ->
        val recNamedRecCount = recNamedRecCountByInductive.getOrElse(inductive.name, { 0 })
        check(recNamedRecCount == 1) {
            "Inductive ${inductive.name.toStringDetailed()} must declare exactly one recursor named ${inductive.name.toStringDetailed()}.rec, got $recNamedRecCount"
        }
    }
    data.recs.forEach { recursor ->
        checkRecursorRules(recursor)
    }
}

context(env: Environment)
private fun analyzeInductiveType(inductive: Inductive.InductiveVal): InductiveTypeInfo {
    val typeBinderCount = inductive.numParams + inductive.numIndices
    val inductiveParamTypes = mutableListOf<Expression>()
    val inductiveParamSortLevels = mutableListOf<Level>()

    val typeTailWhnf = walkForalls(
        expr = inductive.typeExpr,
        expectedBinders = typeBinderCount,
        owner = "Inductive type ${inductive.name}",
    ) { binderIndex, binderType, localCtx ->
        val binderSort = binderType.inferSort(localCtx = localCtx)
        if (binderIndex < inductive.numParams) {
            inductiveParamTypes += binderType
            inductiveParamSortLevels += binderSort
        }
    }

    val typeSort = typeTailWhnf as? Expression.Sort
        ?: error("Inductive type must reduce to Sort after $typeBinderCount binders, got ${typeTailWhnf.toStringDetailed()}")
    return InductiveTypeInfo(inductiveParamTypes, inductiveParamSortLevels, typeSort.level)
}

context(env: Environment)
private fun checkSharedParams(
    referenceInductive: Inductive.InductiveVal,
    referenceInfo: InductiveTypeInfo,
    inductive: Inductive.InductiveVal,
    inductiveInfo: InductiveTypeInfo,
) {
    var referenceLocalCtx: List<Expression> = emptyList()
    var inductiveLocalCtx: List<Expression> = emptyList()
    repeat(referenceInductive.numParams) { paramIndex ->
        val expectedParamType = referenceInfo.paramTypes[paramIndex]
        val actualParamType = inductiveInfo.paramTypes[paramIndex]
        check(actualParamType.isDefEq(expectedParamType, inductiveLocalCtx, referenceLocalCtx)) {
            "Mutual inductive ${inductive.name.toStringDetailed()} parameter #$paramIndex type mismatch with ${referenceInductive.name.toStringDetailed()}: expected ${expectedParamType.toStringDetailed()}, got ${actualParamType.toStringDetailed()}"
        }
        referenceLocalCtx = env.consLocalCtx(expectedParamType, referenceLocalCtx)
        inductiveLocalCtx = env.consLocalCtx(actualParamType, inductiveLocalCtx)
    }
}

context(env: Environment)
private fun checkConstructor(
    constructor: Inductive.ConstructorVal,
    inductive: Inductive.InductiveVal,
    inductiveInfo: InductiveTypeInfo,
    mutualInductiveNames: Set<Name>,
    maxFieldSortLevel: Level,
) {
    check(constructor.inductName == inductive.name) {
        "Constructor ${constructor.name.toStringDetailed()} has wrong inductive target: expected ${inductive.name.toStringDetailed()}, got ${constructor.inductName.toStringDetailed()}"
    }
    check(constructor.numParams == inductive.numParams) {
        "Constructor ${constructor.name.toStringDetailed()} has wrong numParams: expected ${inductive.numParams}, got ${constructor.numParams}"
    }
    check(constructor.hasDistinctLevelParams()) {
        "Duplicate universe parameters in constructor $constructor"
    }
    check(constructor.levelParams.isEqual(inductive.levelParams)) {
        "Constructor ${constructor.name.toStringDetailed()} has mismatched universe parameters"
    }

    val isInductiveProp = inductiveInfo.sortLevel.isLessOrEqual(Level.Zero)
    val ctorBinderCount = constructor.numParams + constructor.numFields
    val ctorTailExpr = walkForalls(
        expr = constructor.typeExpr,
        expectedBinders = ctorBinderCount,
        owner = "Constructor ${constructor.name}",
        reduceExpr = false,
    ) { binderIndex, binderType, localCtx ->
        if (binderIndex < constructor.numParams) {
            val expectedParamType = inductiveInfo.paramTypes.getOrNull(binderIndex)
                ?: error("Missing expected parameter type #$binderIndex for constructor ${constructor.name}")
            check(binderType.isDefEq(expectedParamType, localCtx, localCtx)) {
                "Constructor ${constructor.name} parameter #$binderIndex type mismatch: expected ${expectedParamType.toStringDetailed()}, got ${binderType.toStringDetailed()}"
            }
        } else {
            val fieldSort = binderType.inferSort(localCtx = localCtx)
            check(isInductiveProp || fieldSort.isLessOrEqual(maxFieldSortLevel)) {
                "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} has sort ${fieldSort.toStringDetailed()} above allowed sort ${maxFieldSortLevel.toStringDetailed()}"
            }
            check(!binderType.hasNegativeOccurrenceOf(mutualInductiveNames)) {
                "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} contains a non-positive occurrence of a mutual inductive"
            }
        }
    }

    val [resultHead, resultArgs] = ctorTailExpr.unfoldApp()
    val resultConst = resultHead as? Expression.Const
        ?: error("Constructor ${constructor.name} must end in application of inductive ${inductive.name}, got ${ctorTailExpr.toStringDetailed()}")
    check(
        resultConst.name == inductive.name && resultConst.levels.isEqual(inductive.levelParams) &&
                resultArgs.size == inductive.numParams + inductive.numIndices
    ) {
        "Constructor ${constructor.name} must return ${inductive.name.toStringDetailed()} with its declared universe parameters and arity"
    }

    repeat(inductive.numParams) { paramIndex ->
        val expectedBvar = ctorBinderCount - 1 - paramIndex
        val actualArg = resultArgs[paramIndex]
        check(actualArg is Expression.Bvar && actualArg.bvar == expectedBvar) {
            "Constructor ${constructor.name} result parameter #$paramIndex must be bvar $expectedBvar, got ${actualArg.toStringDetailed()}"
        }
    }

    resultArgs.drop(inductive.numParams).forEach { indexArg ->
        check(!indexArg.containsConst(mutualInductiveNames)) {
            "Constructor ${constructor.name} index argument contains a mutual inductive: ${indexArg.toStringDetailed()}"
        }
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
        val current = if (reduceExpr) currentExpr.whnf() else currentExpr
        val forall = current as? Expression.ForallE
            ?: error("$owner has too few binders: expected $expectedBinders, got $binderIndex")

        onBinder(binderIndex, forall.typeExpr, currentLocalCtx)
        currentLocalCtx = env.consLocalCtx(forall.typeExpr, currentLocalCtx)
        currentExpr = forall.bodyExpr
    }

    return if (reduceExpr) currentExpr.whnf() else currentExpr
}

context(env: Environment)
private fun collectForallContext(
    expr: Expression,
    expectedBinders: Int,
    owner: String,
): Pair<List<Expression>, Expression> {
    var localCtx: List<Expression> = emptyList()
    var currentExpr = expr
    repeat(expectedBinders) { binderIndex ->
        val forall = currentExpr as? Expression.ForallE
            ?: error("$owner has too few binders: expected $expectedBinders, got $binderIndex")
        localCtx = env.consLocalCtx(forall.typeExpr, localCtx)
        currentExpr = forall.bodyExpr
    }
    return localCtx to currentExpr
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
private fun checkRecursorRules(recursor: Inductive.RecursorVal) {
    val majorType = recursor.getMajorBinder().typeExpr
    val [majorTypeHead, majorTypeArgs] = majorType.unfoldApp()
    val majorTypeConst = majorTypeHead as? Expression.Const
        ?: error("Recursor ${recursor.name} major premise type must be const-headed, got ${majorType.toStringDetailed()}")
    val majorInductName = majorTypeConst.name
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
        checkRecursorRuleType(recursor, constructor, rule, majorInductive, majorTypeConst, majorTypeArgs)
    }
    val expectedCtorNames = majorInductive.ctors.map { ctorNameIndex ->
        env.names[ctorNameIndex] ?: error("Constructor name $ctorNameIndex not found")
    }.toSet()
    check(seenCtorNames == expectedCtorNames) {
        "Recursor ${recursor.name} has wrong rule set: expected ${expectedCtorNames.map { it.toStringDetailed() }}, got ${seenCtorNames.map { it.toStringDetailed() }}"
    }
}

context(env: Environment)
private fun checkRecursorRuleType(
    recursor: Inductive.RecursorVal,
    constructor: Inductive.ConstructorVal,
    rule: Inductive.RecursorVal.RecursorRule,
    majorInductive: Inductive.InductiveVal,
    majorTypeConst: Expression.Const,
    majorTypeArgs: List<Expression>,
) {
    val prefixBinderCount = recursor.numParams + recursor.numMotives + recursor.numMinors
    val expectedRuleBinderCount = prefixBinderCount + constructor.numFields
    val inferredRuleType = rule.rhsExpr.inferType()
    val ruleTypeInfo = collectForallContext(
        expr = inferredRuleType,
        expectedBinders = expectedRuleBinderCount,
        owner = "Recursor rule for ${constructor.name}",
    )
    val ruleLocalCtx = ruleTypeInfo.first
    val ruleResultType = ruleTypeInfo.second

    fun binderExpr(outerIndex: Int): Expression {
        return env.addCustomExpr {
            Expression.Bvar(ruleLocalCtx.lastIndex - outerIndex, it)
        }
    }

    val prefixArgs = List(prefixBinderCount, ::binderExpr)
    val fieldArgs = List(constructor.numFields) { fieldIndex ->
        binderExpr(prefixBinderCount + fieldIndex)
    }

    check(majorTypeArgs.size >= constructor.numParams) {
        "Recursor ${recursor.name} major premise type has too few args for constructor ${constructor.name}: expected at least ${constructor.numParams}, got ${majorTypeArgs.size}"
    }
    val paramArgs = majorTypeArgs.take(constructor.numParams).map { paramArg ->
        paramArg.dropOuterBinders(recursor.numIndices).lift(constructor.numFields)
    }

    val constructorNameIndex = env.nameIndices[constructor.name]
        ?: error("Constructor name index for ${constructor.name} not found")
    val constructorExpr = env.addCustomExpr {
        Expression.Const(_name = constructorNameIndex, us = majorTypeConst.levels.map { it.il }, ie = it)
    }
    val majorExpr = constructorExpr.applyArgs(paramArgs + fieldArgs)
    val majorType = majorExpr.inferType(localCtx = ruleLocalCtx).whnf()
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
        .whnf()

    check(ruleResultType.isDefEq(expectedResultType, ruleLocalCtx, ruleLocalCtx)) {
        "Recursor rule for ${constructor.name} has wrong result type: expected ${expectedResultType.toStringDetailed()}, got ${ruleResultType.toStringDetailed()}"
    }
}

context(env: Environment)
fun Expression.applyArgs(args: List<Expression>): Expression {
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
private fun Expression.containsConst(targetNames: Set<Name>): Boolean {
    return when (this) {
        is Expression.App -> this.fnExpr.containsConst(targetNames) || this.argExpr.containsConst(targetNames)
        is Expression.Const -> this.name in targetNames
        is Expression.ForallE -> this.typeExpr.containsConst(targetNames) || this.bodyExpr.containsConst(targetNames)
        is Expression.Lam -> this.typeExpr.containsConst(targetNames) || this.bodyExpr.containsConst(targetNames)
        is Expression.LetE ->
            this.typeExpr.containsConst(targetNames) ||
                    this.valueExpr.containsConst(targetNames) ||
                    this.bodyExpr.containsConst(targetNames)

        is Expression.Mdata -> this.expr.containsConst(targetNames)
        is Expression.Proj -> this.structExpr.containsConst(targetNames)
        is Expression.Bvar, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> false
    }
}

context(env: Environment)
private fun Expression.containsConst(targetName: Name): Boolean = this.containsConst(setOf(targetName))

context(env: Environment)
private fun Expression.hasNegativeOccurrenceOf(targetNames: Set<Name>, polarity: Int = 1): Boolean {
    return when (this) {
        is Expression.App ->
            this.fnExpr.hasNegativeOccurrenceOf(targetNames, polarity) ||
                    this.argExpr.hasNegativeOccurrenceOf(targetNames, polarity)

        is Expression.Const -> this.name in targetNames && polarity < 0

        is Expression.ForallE ->
            this.typeExpr.hasNegativeOccurrenceOf(targetNames, -polarity) ||
                    this.bodyExpr.hasNegativeOccurrenceOf(targetNames, polarity)

        is Expression.Lam ->
            this.typeExpr.hasNegativeOccurrenceOf(targetNames, -polarity) ||
                    this.bodyExpr.hasNegativeOccurrenceOf(targetNames, polarity)

        is Expression.LetE ->
            this.typeExpr.hasNegativeOccurrenceOf(targetNames, polarity) ||
                    this.valueExpr.hasNegativeOccurrenceOf(targetNames, polarity) ||
                    this.bodyExpr.hasNegativeOccurrenceOf(targetNames, polarity)

        is Expression.Mdata -> this.expr.hasNegativeOccurrenceOf(targetNames, polarity)
        is Expression.Proj -> this.structExpr.hasNegativeOccurrenceOf(targetNames, polarity)
        is Expression.Bvar, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> false
    }
}
