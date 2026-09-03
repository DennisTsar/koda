package io.github.opletter.koda

private data class InductiveTypeInfo(
    val paramTypes: List<Expression>,
    val sortLevel: Level,
)

internal inline val Inductive.RecursorVal.ruleArgsPrefixSize: Int
    get() = numParams + numMotives + numMinors

internal inline val Inductive.RecursorVal.majorArgIndex: Int
    get() = ruleArgsPrefixSize + numIndices

context(env: Environment)
fun checkInductive(data: Inductive) {
    check(data.types.isNotEmpty()) {
        "Inductive block must contain at least one type"
    }

    val inductives = data.types
    val blockNumParams = inductives.first().numParams
    val blockNumNested = inductives.first().numNested
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
        inductive.checkLevelParams(listOf(inductive.typeExpr))
        check(inductive.numParams == blockNumParams) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong numParams: expected $blockNumParams, got ${inductive.numParams}"
        }
        check(inductive.numNested == blockNumNested) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong numNested: expected $blockNumNested, got ${inductive.numNested}"
        }
        check(inductive.all == blockNameIndices) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong all list: expected $blockNameIndices, got ${inductive.all}"
        }
        check(inductive.levelParams.isEqual(blockLevelParams)) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has mismatched universe parameters"
        }
    }

    checkUniformInductiveOccurrences(data.ctors, blockNameSet, blockNumParams, blockLevelParams)

    val inductiveInfos = inductives.associateWith { analyzeInductiveType(it) }
    val firstInductive = inductives.first()
    val firstInfo = inductiveInfos.getValue(firstInductive)
    inductives.drop(1).forEach { inductive ->
        val inductiveInfo = inductiveInfos.getValue(inductive)
        checkSharedParams(firstInductive, firstInfo, inductive, inductiveInfo)
        check(inductiveInfo.sortLevel.isEqual(firstInfo.sortLevel)) {
            "Mutual inductive ${inductive.name.toStringDetailed()} lives in a different universe than ${firstInductive.name.toStringDetailed()}"
        }
    }
    val motiveCount = inductives.size + blockNumNested

    data.registerInto(env)
    inductives.forEach { inductive ->
        env.declTypeByName[inductive.name] = inductive.typeExpr
    }

    val ctorsByInductive = data.ctors.groupBy { it.inductName }
    check(ctorsByInductive.keys.all { it in blockNameSet }) {
        "Mutual inductive block has constructor for an unrelated type: ${ctorsByInductive.keys.map { it.toStringDetailed() }}"
    }
    val singletonEliminationByInductive = mutableMapOf<Inductive.InductiveVal, Boolean>()
    inductives.forEach { inductive ->
        val inductiveInfo = inductiveInfos.getValue(inductive)
        val constructors = (ctorsByInductive[inductive.name] ?: emptyList()).sortedBy { it.cidx }
        check(constructors.size == inductive.ctors.size) {
            "Mutual inductive ${inductive.name.toStringDetailed()} has wrong constructor count: expected ${inductive.ctors.size}, got ${constructors.size}"
        }
        val singletonEliminationChecks = constructors.mapIndexed { ctorIndex, constructor ->
            constructor.checkLevelParams(listOf(constructor.typeExpr))
            check(constructor.cidx == ctorIndex) {
                "Constructor ${constructor.name.toStringDetailed()} has wrong cidx: expected $ctorIndex, got ${constructor.cidx}"
            }
            val constructorNameIndex = env.nameIndices[constructor.name]
                ?: error("Constructor name index for ${constructor.name.toStringDetailed()} not found")
            check(inductive.ctors[ctorIndex] == constructorNameIndex) {
                "Mutual inductive ${inductive.name.toStringDetailed()} constructor list mismatch at #$ctorIndex"
            }
            val supportsSingletonElimination =
                checkConstructor(constructor, inductive, inductiveInfo, blockNameSet)
            env.declTypeByName[constructor.name] = constructor.typeExpr
            supportsSingletonElimination
        }
        singletonEliminationByInductive[inductive] = when (constructors.size) {
            0 -> true
            1 -> singletonEliminationChecks.single()
            else -> false
        }
    }
    val eliminatesToSort = inductives.all { inductiveInfos.getValue(it).sortLevel.isDefinitelyNonzero() } ||
            motiveCount == 1 && singletonEliminationByInductive.getValue(firstInductive)
    inductives.forEach { inductive ->
        env.eliminatesToSortByInductive[inductive.name] = eliminatesToSort
    }

    val inductivesMissingRecursor = blockNameSet.toMutableSet()
    data.recs.forEach { recursor ->
        check(recursor.all == blockNameIndices) {
            "Recursor ${recursor.name.toStringDetailed()} has wrong all list: expected $blockNameIndices, got ${recursor.all}"
        }
        check(recursor.numParams == blockNumParams) {
            "Recursor ${recursor.name.toStringDetailed()} has wrong numParams: expected $blockNumParams, got ${recursor.numParams}"
        }
        check(recursor.numMotives == motiveCount) {
            "Recursor ${recursor.name.toStringDetailed()} has wrong numMotives: expected $motiveCount, got ${recursor.numMotives}"
        }
        recursor.checkLevelParams(
            buildList {
                add(recursor.typeExpr)
                recursor.rules.forEach { add(it.rhsExpr) }
            }
        )

        val recName = recursor.name as? Name.Str
            ?: error("Recursor name must be a string name, got ${recursor.name}")
        val recParent = env.names[recName.pre]
            ?: error("Recursor ${recursor.name} has missing parent name index ${recName.pre}")
        check(recParent in blockNameSet) {
            "Recursor ${recursor.name.toStringDetailed()} must be in one of the mutual inductive namespaces ${blockNames.map { it.toStringDetailed() }}"
        }
        if (recName.str == "rec") {
            check(inductivesMissingRecursor.remove(recParent)) {
                "Inductive ${recParent.toStringDetailed()} has multiple recursors named ${recParent.toStringDetailed()}.rec"
            }
        }
        env.declTypeByName[recursor.name] = recursor.typeExpr
    }
    check(inductivesMissingRecursor.isEmpty()) {
        "Inductives missing a .rec recursor: ${inductivesMissingRecursor.map { it.toStringDetailed() }}"
    }
    val recursorsByName = data.recs.associateBy { it.name }
    data.recs.forEach { recursor ->
        checkRecursorRules(recursor, recursorsByName)
    }
}

context(env: Environment)
private fun analyzeInductiveType(inductive: Inductive.InductiveVal): InductiveTypeInfo {
    val typeBinderCount = inductive.numParams + inductive.numIndices
    val inductiveParamTypes = mutableListOf<Expression>()

    val typeTailWhnf = walkForalls(
        expr = inductive.typeExpr,
        expectedBinders = typeBinderCount,
        owner = "Inductive type ${inductive.name}",
    ) { binderIndex, binderType, localCtx ->
        val _ = binderType.inferSort(localCtx = localCtx)
        if (binderIndex < inductive.numParams) {
            inductiveParamTypes += binderType
        }
    }.first

    val typeSort = typeTailWhnf as? Expression.Sort
        ?: error("Inductive type must reduce to Sort after $typeBinderCount binders, got ${typeTailWhnf.toStringDetailed()}")
    return InductiveTypeInfo(inductiveParamTypes, typeSort.level)
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
): Boolean {
    val _ = constructor.typeExpr.inferSort()
    check(constructor.inductName == inductive.name) {
        "Constructor ${constructor.name.toStringDetailed()} has wrong inductive target: expected ${inductive.name.toStringDetailed()}, got ${constructor.inductName.toStringDetailed()}"
    }
    check(constructor.numParams == inductive.numParams) {
        "Constructor ${constructor.name.toStringDetailed()} has wrong numParams: expected ${inductive.numParams}, got ${constructor.numParams}"
    }
    check(constructor.levelParams.isEqual(inductive.levelParams)) {
        "Constructor ${constructor.name.toStringDetailed()} has mismatched universe parameters"
    }

    val isInductiveProp = inductiveInfo.sortLevel.isLessOrEqual(Level.Zero)
    val ctorBinderCount = constructor.numParams + constructor.numFields
    val fieldSortLevels = mutableListOf<Level>()
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
            fieldSortLevels += fieldSort
            check(isInductiveProp || fieldSort.isLessOrEqual(inductiveInfo.sortLevel)) {
                "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} has sort ${fieldSort.toStringDetailed()} above allowed sort ${inductiveInfo.sortLevel.toStringDetailed()}"
            }
            check(
                inductive.isRec ||
                        !binderType.whnf(localCtx = localCtx)
                            .containsTarget(PositivityTarget.Inductives(mutualInductiveNames, emptyList()))
            ) {
                "Recursive inductive ${inductive.name.toStringDetailed()} is marked nonrecursive"
            }
            check(
                binderType.isStrictlyPositive(
                    PositivityTarget.Inductives(
                        mutualInductiveNames,
                        List(inductive.numParams) { localCtx.lastIndex - it },
                    ),
                    localCtx,
                    mutualInductiveNames,
                )
            ) {
                "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} contains a non-positive occurrence of a mutual inductive"
            }
        }
    }.first

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
        check(!indexArg.containsTarget(PositivityTarget.Inductives(mutualInductiveNames, emptyList()))) {
            "Constructor ${constructor.name} index argument contains a mutual inductive: ${indexArg.toStringDetailed()}"
        }
    }

    return fieldSortLevels.withIndex().all { field ->
        field.value.isLessOrEqual(Level.Zero) || resultArgs.any { resultArg ->
            resultArg is Expression.Bvar && resultArg.bvar == constructor.numFields - 1 - field.index
        }
    }
}

context(env: Environment)
private fun walkForalls(
    expr: Expression,
    expectedBinders: Int,
    owner: String,
    reduceExpr: Boolean = true,
    onBinder: (binderIndex: Int, binderType: Expression, localCtx: List<Expression>) -> Unit = { _, _, _ -> },
): Pair<Expression, List<Expression>> {
    var currentExpr = expr
    var currentLocalCtx: List<Expression> = emptyList()

    repeat(expectedBinders) { binderIndex ->
        val current = if (reduceExpr) currentExpr.whnf(localCtx = currentLocalCtx) else currentExpr
        val forall = current as? Expression.ForallE
            ?: error("$owner has too few binders: expected $expectedBinders, got $binderIndex")

        onBinder(binderIndex, forall.typeExpr, currentLocalCtx)
        currentLocalCtx = env.consLocalCtx(forall.typeExpr, currentLocalCtx)
        currentExpr = forall.bodyExpr
    }

    return (if (reduceExpr) currentExpr.whnf(localCtx = currentLocalCtx) else currentExpr) to currentLocalCtx
}

context(env: Environment)
fun Inductive.RecursorVal.getMajorBinder(): Expression.ForallE {
    val tailExpr = walkForalls(this.typeExpr, majorArgIndex, "Recursor ${this.name}", reduceExpr = false).first
    return tailExpr as? Expression.ForallE
        ?: error("Recursor ${this.name} is missing a major premise binder")
}

context(env: Environment)
private fun checkRecursorRules(
    recursor: Inductive.RecursorVal,
    recursorsByName: Map<Name, Inductive.RecursorVal>,
) {
    val _ = recursor.typeExpr.inferSort()
    val majorType = recursor.getMajorBinder().typeExpr
    val [majorTypeHead, majorTypeArgs] = majorType.unfoldApp()
    val majorTypeConst = majorTypeHead as? Expression.Const
        ?: error("Recursor ${recursor.name} major premise type must be const-headed, got ${majorType.toStringDetailed()}")
    val majorInductName = majorTypeConst.name
    val majorInductNameIndex = env.nameIndices[majorInductName]
        ?: error("Major inductive name index for ${majorInductName.toStringDetailed()} not found")
    val majorInductive = env.declarations[majorInductNameIndex] as? Inductive.InductiveVal
        ?: error("Recursor ${recursor.name} major premise type ${majorInductName.toStringDetailed()} is not an inductive")
    val canEliminateToSort = env.eliminatesToSortByInductive[majorInductName]
        ?: error("Missing elimination information for inductive ${majorInductName.toStringDetailed()}")
    val recursorName = recursor.name as? Name.Str
        ?: error("Recursor name must be a string name, got ${recursor.name}")
    if (recursorName.str == "rec" && env.names[recursorName.pre] == majorInductName) {
        val inductiveLevelParams = majorInductive.levelParams
        val recursorLevelParams = recursor.levelParams
        val hasExpectedLevelParams = if (canEliminateToSort) {
            recursorLevelParams.size == inductiveLevelParams.size + 1 &&
                    recursorLevelParams.drop(1).isEqual(inductiveLevelParams)
        } else {
            recursorLevelParams.isEqual(inductiveLevelParams)
        }
        check(hasExpectedLevelParams) {
            "Recursor ${recursor.name} has universe parameters incompatible with its elimination level"
        }
    }
    if (!canEliminateToSort) {
        walkForalls(
            recursor.typeExpr,
            recursor.numParams + recursor.numMotives,
            "Recursor ${recursor.name}",
            reduceExpr = false,
        ) { binderIndex, binderType, localCtx ->
            if (binderIndex >= recursor.numParams) {
                val motiveLevel = binderType.resultSortLevel(localCtx, "Recursor ${recursor.name} motive")
                check(motiveLevel.isLessOrEqual(Level.Zero)) {
                    "Recursor ${recursor.name} cannot eliminate into ${motiveLevel.toStringDetailed()}"
                }
            }
        }
    }
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
        checkRecursorRuleType(
            recursor,
            constructor,
            rule,
            majorInductive,
            majorTypeConst,
            majorTypeArgs,
            recursorsByName,
        )
    }
    val expectedCtorNames = majorInductive.ctors.map { ctorNameIndex ->
        env.names[ctorNameIndex] ?: error("Constructor name $ctorNameIndex not found")
    }.toSet()
    check(seenCtorNames == expectedCtorNames) {
        "Recursor ${recursor.name} has wrong rule set: expected ${expectedCtorNames.map { it.toStringDetailed() }}, got ${seenCtorNames.map { it.toStringDetailed() }}"
    }
}

context(env: Environment)
private fun Expression.resultSortLevel(initialLocalCtx: List<Expression>, owner: String): Level {
    var current = this
    var localCtx = initialLocalCtx
    while (true) {
        when (val normalized = current.whnf(localCtx = localCtx)) {
            is Expression.ForallE -> {
                localCtx = env.consLocalCtx(normalized.typeExpr, localCtx)
                current = normalized.bodyExpr
            }

            is Expression.Sort -> return normalized.level
            else -> error("$owner must end in a sort, got ${normalized.toStringDetailed()}")
        }
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
    recursorsByName: Map<Name, Inductive.RecursorVal>,
) {
    val prefixBinderCount = recursor.ruleArgsPrefixSize
    val expectedRuleBinderCount = prefixBinderCount + constructor.numFields
    checkStructuralRecursorCalls(
        rule.rhsExpr,
        recursorsByName,
        prefixBinderCount,
        constructor.numFields,
        "Recursor rule for ${constructor.name}",
    )
    val inferredRuleType = rule.rhsExpr.inferType()
    val [ruleResultType, ruleLocalCtx] = walkForalls(
        expr = inferredRuleType,
        expectedBinders = expectedRuleBinderCount,
        owner = "Recursor rule for ${constructor.name}",
        reduceExpr = false,
    )

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
    val majorType = majorExpr.inferType(localCtx = ruleLocalCtx).whnf(localCtx = ruleLocalCtx)
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
        .whnf(localCtx = ruleLocalCtx)

    check(ruleResultType.isDefEq(expectedResultType, ruleLocalCtx, ruleLocalCtx)) {
        "Recursor rule for ${constructor.name} has wrong result type: expected ${expectedResultType.toStringDetailed()}, got ${ruleResultType.toStringDetailed()}"
    }
}

private data class SyntaxFrame(val expression: Expression, val binderDepth: Int)

private enum class SyntaxVisit { Descend, Arguments, Skip }

context(env: Environment)
private inline fun Expression.walkSyntax(
    visit: (expression: Expression, binderDepth: Int, head: Expression, args: List<Expression>) -> SyntaxVisit,
) {
    val stack = ArrayDeque<SyntaxFrame>()
    stack.add(SyntaxFrame(this, 0))
    while (stack.isNotEmpty()) {
        val [expression, binderDepth] = stack.removeLast()
        val [head, args] = expression.unfoldApp()
        when (visit(expression, binderDepth, head, args)) {
            SyntaxVisit.Skip -> continue
            SyntaxVisit.Arguments -> {
                args.forEach { stack.add(SyntaxFrame(it, binderDepth)) }
                continue
            }

            SyntaxVisit.Descend -> {}
        }

        if (expression is Expression.App) {
            stack.add(SyntaxFrame(head, binderDepth))
            args.forEach { stack.add(SyntaxFrame(it, binderDepth)) }
            continue
        }
        when (expression) {
            is Expression.ForallE -> {
                stack.add(SyntaxFrame(expression.typeExpr, binderDepth))
                stack.add(SyntaxFrame(expression.bodyExpr, binderDepth + 1))
            }

            is Expression.Lam -> {
                stack.add(SyntaxFrame(expression.typeExpr, binderDepth))
                stack.add(SyntaxFrame(expression.bodyExpr, binderDepth + 1))
            }

            is Expression.LetE -> {
                stack.add(SyntaxFrame(expression.typeExpr, binderDepth))
                stack.add(SyntaxFrame(expression.valueExpr, binderDepth))
                stack.add(SyntaxFrame(expression.bodyExpr, binderDepth + 1))
            }

            is Expression.Mdata -> stack.add(SyntaxFrame(expression.expr, binderDepth))
            is Expression.Proj -> stack.add(SyntaxFrame(expression.structExpr, binderDepth))
            is Expression.App, is Expression.Bvar, is Expression.Const, is Expression.NatVal,
            is Expression.Sort, is Expression.StrVal -> {}
        }
    }
}

context(env: Environment)
private fun checkStructuralRecursorCalls(
    expression: Expression,
    recursorsByName: Map<Name, Inductive.RecursorVal>,
    prefixBinderCount: Int,
    numFields: Int,
    owner: String,
) {
    val seen = mutableSetOf<Long>()
    expression.walkSyntax { current, binderDepth, head, args ->
        val key = (binderDepth.toLong() shl 32) xor (current.ie.toLong() and 0xffffffffL)
        if (!seen.add(key)) return@walkSyntax SyntaxVisit.Skip
        val calledRecursor = (head as? Expression.Const)?.let { recursorsByName[it.name] }
        if (calledRecursor != null) {
            val majorIndex = calledRecursor.majorArgIndex
            check(args.size > majorIndex) {
                "$owner contains an under-applied recursive call to ${calledRecursor.name}"
            }
            val [majorHead] = args[majorIndex].unfoldApp()
            val majorBvar = majorHead as? Expression.Bvar
            val isConstructorField = majorBvar != null &&
                    binderDepth >= prefixBinderCount + numFields &&
                    (0 until numFields).any { fieldIndex ->
                        majorBvar.bvar == binderDepth - 1 - prefixBinderCount - fieldIndex
                    }
            check(isConstructorField) {
                "$owner calls ${calledRecursor.name} on an expression that is not a constructor field"
            }
            SyntaxVisit.Arguments
        } else {
            SyntaxVisit.Descend
        }
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
private fun checkUniformInductiveOccurrences(
    constructors: List<Inductive.ConstructorVal>,
    inductiveNames: Set<Name>,
    numParams: Int,
    levelParams: List<Level.Param>,
) {
    val levelParamIndices = levelParams.map { it.il }
    constructors.forEach { constructor ->
        constructor.typeExpr.walkSyntax { _, binderDepth, head, args ->
            if (head is Expression.Const && head.name in inductiveNames) {
                val isUniform = args.size >= numParams && binderDepth >= numParams &&
                        head.levels.map { it.il } == levelParamIndices &&
                        (0 until numParams).all { paramIndex ->
                            val arg = args[paramIndex]
                            arg is Expression.Bvar && arg.bvar == binderDepth - 1 - paramIndex
                        }
                check(isUniform) {
                    "Invalid occurrence of ${head.name.toStringDetailed()} in constructor ${constructor.name}: " +
                            "it must use the mutual declaration's parameters and universe levels"
                }
                SyntaxVisit.Arguments
            } else {
                SyntaxVisit.Descend
            }
        }
    }
}

private sealed interface PositivityTarget {
    data class Inductives(val names: Set<Name>, val paramBvars: List<Int>) : PositivityTarget
    data class Parameter(val bvar: Int) : PositivityTarget
}

private data class PositivityRequest(
    val expression: Expression,
    val localCtx: List<Expression>,
    val target: PositivityTarget,
    val currentInductiveNames: Set<Name>,
)

private fun PositivityTarget.underBinder(): PositivityTarget = when (this) {
    is PositivityTarget.Inductives -> copy(paramBvars = paramBvars.map { it + 1 })
    is PositivityTarget.Parameter -> copy(bvar = bvar + 1)
}

context(env: Environment)
private fun Expression.containsTarget(target: PositivityTarget): Boolean {
    var found = false
    walkSyntax { expression, binderDepth, _, _ ->
        found = found || when (target) {
            is PositivityTarget.Inductives -> expression is Expression.Const && expression.name in target.names
            is PositivityTarget.Parameter ->
                expression is Expression.Bvar && expression.bvar == target.bvar + binderDepth
        }
        if (found) SyntaxVisit.Skip else SyntaxVisit.Descend
    }
    return found
}

context(env: Environment)
private fun Expression.isStrictlyPositive(
    target: PositivityTarget,
    localCtx: List<Expression>,
    currentInductiveNames: Set<Name>,
): Boolean {
    val check = DeepRecursiveFunction<PositivityRequest, Boolean> { request ->
        val expression = request.expression.whnf(localCtx = request.localCtx)
        if (
            request.target is PositivityTarget.Parameter && expression is Expression.Bvar &&
            expression.bvar == request.target.bvar
        ) {
            return@DeepRecursiveFunction true
        }

        val [head, args] = expression.unfoldApp()
        if (
            request.target is PositivityTarget.Parameter && head is Expression.Bvar &&
            head.bvar == request.target.bvar
        ) {
            return@DeepRecursiveFunction args.none { it.containsTarget(request.target) }
        }
        val headConst = head as? Expression.Const
        val currentInductive = if (headConst?.name in request.currentInductiveNames) {
            headConst?.decl as? Inductive.InductiveVal
        } else {
            null
        }
        if (currentInductive != null) {
            if (
                args.size != currentInductive.numParams + currentInductive.numIndices ||
                args.drop(currentInductive.numParams).any { it.containsTarget(request.target) }
            ) {
                return@DeepRecursiveFunction false
            }
            if (request.target is PositivityTarget.Inductives) {
                if (request.target.paramBvars.size != currentInductive.numParams) {
                    return@DeepRecursiveFunction false
                }
                for (paramIndex in request.target.paramBvars.indices) {
                    val arg = args[paramIndex]
                    if (arg !is Expression.Bvar || arg.bvar != request.target.paramBvars[paramIndex]) {
                        return@DeepRecursiveFunction false
                    }
                }
            }
            return@DeepRecursiveFunction true
        }

        if (!expression.containsTarget(request.target)) return@DeepRecursiveFunction true
        if (expression is Expression.ForallE || expression is Expression.Lam) {
            val binderType = when (expression) {
                is Expression.ForallE -> expression.typeExpr
                is Expression.Lam -> expression.typeExpr
            }
            val binderBody = when (expression) {
                is Expression.ForallE -> expression.bodyExpr
                is Expression.Lam -> expression.bodyExpr
            }
            if (binderType.containsTarget(request.target)) return@DeepRecursiveFunction false
            return@DeepRecursiveFunction callRecursive(
                request.copy(
                    expression = binderBody,
                    localCtx = env.consLocalCtx(binderType, request.localCtx),
                    target = request.target.underBinder(),
                )
            )
        }

        val container = headConst?.decl as? Inductive.InductiveVal
            ?: return@DeepRecursiveFunction false
        if (args.size != container.numParams + container.numIndices) return@DeepRecursiveFunction false
        for (argIndex in args.indices) {
            val arg = args[argIndex]
            if (!arg.containsTarget(request.target)) continue
            if (
                argIndex >= container.numParams ||
                !container.isStrictlyPositiveInParameter(argIndex) ||
                !callRecursive(request.copy(expression = arg))
            ) {
                return@DeepRecursiveFunction false
            }
        }
        true
    }

    return check(PositivityRequest(this, localCtx, target, currentInductiveNames))
}

context(env: Environment)
private fun Inductive.InductiveVal.isStrictlyPositiveInParameter(paramIndex: Int): Boolean {
    val key = name to paramIndex
    env.strictlyPositiveInductiveParams[key]?.let { return it }
    if (paramIndex !in 0 until numParams) return false

    val mutualInductives = all.map { nameIndex ->
        env.declarations[nameIndex] as? Inductive.InductiveVal ?: return false
    }
    val mutualNames = mutualInductives.mapTo(mutableSetOf()) { it.name }
    val result = mutualInductives.all { mutual ->
        mutual.ctors.all { constructorIndex ->
            val constructor = env.declarations[constructorIndex] as? Inductive.ConstructorVal
                ?: return@all false
            var constructorType = constructor.typeExpr
            var localCtx: List<Expression> = emptyList()
            (0 until constructor.numParams + constructor.numFields).all { binderIndex ->
                val binder = constructorType as? Expression.ForallE ?: return@all false
                val fieldIsPositive = binderIndex < constructor.numParams || binder.typeExpr.isStrictlyPositive(
                    PositivityTarget.Parameter(localCtx.lastIndex - paramIndex),
                    localCtx,
                    mutualNames,
                )
                localCtx = env.consLocalCtx(binder.typeExpr, localCtx)
                constructorType = binder.bodyExpr
                fieldIsPositive
            }
        }
    }
    mutualNames.forEach { mutualName ->
        env.strictlyPositiveInductiveParams[mutualName to paramIndex] = result
    }
    return result
}