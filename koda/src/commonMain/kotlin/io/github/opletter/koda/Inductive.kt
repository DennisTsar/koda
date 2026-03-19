package io.github.opletter.koda

private data class ForallWalkResult(
    val tailExpr: Expression,
    val levelSubst: Map<Int, Level>,
)

context(env: Environment)
fun checkInductive(data: Inductive) {
    // (1): no duplicate universe parameters
    check(data.type.levelParams.toSet().size == data.type.levelParams.size) {
        "Duplicate universe parameters in $data"
    }

    val inductive = data.type
    val typeBinderCount = inductive.numParams + inductive.numIndices
    val inductiveParamTypes = mutableListOf<Expression>()

    // One pass over the inductive type telescope.
    val typeWalk = walkForalls(
        expr = inductive.typeExpr,
        expectedBinders = typeBinderCount,
        owner = "Inductive type ${inductive.name}",
    ) { binderIndex, binderType, levelSubst, localCtx ->
        // Every binder domain in the type constructor must itself be a type.
        val _ = binderType.inferSort(levelSubst, localCtx)
        if (binderIndex < inductive.numParams) {
            inductiveParamTypes += binderType
        }
    }

    val typeTailWhnf = typeWalk.tailExpr.reduce(typeWalk.levelSubst)
    val typeSort = typeTailWhnf.expr as? Expression.Sort
        ?: error("Inductive type must reduce to Sort after $typeBinderCount binders, got ${typeTailWhnf.expr.toStringDetailed()}")
    val inductiveSortLevel = typeSort.level.instantiateLevelParams(typeTailWhnf.levelSubst)
    val isInductiveProp = inductiveSortLevel.isLessOrEqual(Level.Zero)

    println("boom ${data.type.name}")
    data.registerInto(env)
    env.declTypeByName[data.type.name] = data.type.typeExpr

    data.ctors.forEach { constructor ->
        println("boom ${constructor.name}")
        // Basic declaration-level consistency.
        check(constructor.inductName == inductive.name) {
            "Constructor ${constructor.name} has wrong inductive target: expected ${inductive.name}, got ${constructor.inductName}"
        }
        check(constructor.numParams == inductive.numParams) {
            "Constructor ${constructor.name} has wrong numParams: expected ${inductive.numParams}, got ${constructor.numParams}"
        }
        check(constructor.levelParams.toSet().size == constructor.levelParams.size) {
            "Duplicate universe parameters in constructor $constructor"
        }

        val ctorBinderCount = constructor.numParams + constructor.numFields
        val ctorWalk = walkForalls(
            expr = constructor.typeExpr,
            expectedBinders = ctorBinderCount,
            owner = "Constructor ${constructor.name}",
            reduceExpr = false,
        ) { binderIndex, binderType, levelSubst, localCtx ->
            if (binderIndex < constructor.numParams) {
                // Parameter section must exactly match the inductive parameters.
                val expectedParamType = inductiveParamTypes.getOrNull(binderIndex)
                    ?: error("Missing expected parameter type #$binderIndex for constructor ${constructor.name}")
                check(binderType.isDefEq(expectedParamType, levelSubst, levelSubst)) {
                    "Constructor ${constructor.name} parameter #$binderIndex type mismatch: expected ${expectedParamType.toStringDetailed()}, got ${binderType.toStringDetailed()}"
                }
            } else {
                // Field domain must be a type and satisfy universe + positivity checks.
                val fieldSort = binderType.inferSort(levelSubst, localCtx)
                check(isInductiveProp || fieldSort.isLessOrEqual(inductiveSortLevel)) {
                    "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} has sort ${fieldSort.toStringDetailed()} above inductive sort ${inductiveSortLevel.toStringDetailed()}"
                }
                check(!binderType.hasNegativeOccurrenceOf(inductive.name)) {
                    "Constructor ${constructor.name} field #${binderIndex - constructor.numParams} contains a non-positive occurrence of inductive ${inductive.name}"
                }
            }
        }

        val ctorTailExpr = ctorWalk.tailExpr
        check(ctorTailExpr !is Expression.ForallE) {
            "Constructor ${constructor.name} has too many binders: expected $ctorBinderCount"
        }

        // Constructor result must be an application of the inductive with valid args.
        val unfoldedResult = ctorTailExpr.unfoldApp()
        val resultHead: Expression = unfoldedResult.first
        val resultArgs: List<Expression> = unfoldedResult.second
        val resultConst = resultHead as? Expression.Const
            ?: error("Constructor ${constructor.name} must end in application of inductive ${inductive.name}, got ${ctorTailExpr.toStringDetailed()}")

        check(resultConst.name == inductive.name) {
            "Constructor ${constructor.name} must return inductive ${inductive.name}, got ${resultConst.name}"
        }
        check(resultConst.levels.size == inductive.levelParams.size) {
            "Constructor ${constructor.name} has wrong number of universe args in result: expected ${inductive.levelParams.size}, got ${resultConst.levels.size}"
        }
        inductive.levelParams.indices.forEach { i ->
            check(resultConst.levels[i].isEqual(inductive.levelParams[i])) {
                "Constructor ${constructor.name} result has wrong universe arg #$i: expected ${inductive.levelParams[i].toStringDetailed()}, got ${resultConst.levels[i].toStringDetailed()}"
            }
        }

        val expectedResultArgs = inductive.numParams + inductive.numIndices
        check(resultArgs.size == expectedResultArgs) {
            "Constructor ${constructor.name} result has wrong arg count: expected $expectedResultArgs, got ${resultArgs.size}"
        }

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

        println("boom2 ${constructor.name}")
        env.declTypeByName[constructor.name] = constructor.typeExpr
    }
    data.recs.forEach { rec ->
        env.declTypeByName[rec.name] = rec.typeExpr
    }

}

context(env: Environment)
private fun walkForalls(
    expr: Expression,
    expectedBinders: Int,
    owner: String,
    reduceExpr: Boolean = true,
    onBinder: (binderIndex: Int, binderType: Expression, levelSubst: Map<Int, Level>, localCtx: List<Expression>) -> Unit,
): ForallWalkResult {
    var currentExpr = expr
    var currentLevelSubst: Map<Int, Level> = emptyMap()
    var currentLocalCtx: List<Expression> = emptyList()

    repeat(expectedBinders) { binderIndex ->
        val current = if (reduceExpr) {
            val whnf = currentExpr.reduce(currentLevelSubst)
            currentLevelSubst = whnf.levelSubst
            whnf.expr
        } else {
            currentExpr
        }
        val forall = current as? Expression.ForallE
            ?: error("$owner has too few binders: expected $expectedBinders, got $binderIndex")

        onBinder(binderIndex, forall.typeExpr, currentLevelSubst, currentLocalCtx)
        currentLocalCtx = listOf(forall.typeExpr) + currentLocalCtx
        currentExpr = forall.bodyExpr
    }

    return ForallWalkResult(
        tailExpr = currentExpr,
        levelSubst = currentLevelSubst,
    )
}

context(env: Environment)
private fun Expression.unfoldApp(): Pair<Expression, List<Expression>> {
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

        else -> false
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

        else -> false
    }
}
