package io.github.opletter.koda

fun typeCheck(data: Sequence<ExportType>) {
    val env = Environment()
//    typeCheck(data, env = env)
    context(env) {
        _typeCheck(data)
    }
}

context(env: Environment)
fun _typeCheck(rawData: Sequence<ExportType>) {
    val debugTimingRanges = emptyList<IntRange>()
    rawData.forEachIndexed { index, data ->
        //i: progress = 1000000 13.462160800s
        //i: progress = 1100000 24.175118s
        //..
        //i: progress = 1122250 24.465904400s
        //i: progress = 1122251 36.557328900s
        //...
        //i: progress = 1122611 36.558250900s
        //i: progress = 1122612 48.691833300s
        if (index != 0 && index % 1_000_000 == 0) {
            println("i: progress = $index ${env.clock.elapsedNow()}")
            println(" (checked ${env.counter} declarations)")
        }
        val shouldTimeDeclaration = data is Declaration && debugTimingRanges.any { index in it }
        if (env.shouldLog || shouldTimeDeclaration) {
            println("started: ${env.clock.elapsedNow()}")
            val dataName = (data as? NamedDecl)?.name?.toStringDetailed() ?: data::class.simpleName
            println("i: index=$index")
            println("$dataName $data")
            println("---")
        }
        when (data) {
            is Name -> {
                data.registerInto(env)
            }

            is Level -> {
                data.registerInto(env)
            }

            is Expression -> {
                data.registerInto(env)
            }

            is Declaration -> {
                // (1): "the declaration is not already declared in the environment"
                data.registerInto(env)
                // (2): "has no duplicate universe parameters"
                // not the most efficient check but probably doesn't matter?
                check(data.levelParams.toSet().size == data.levelParams.size) { "Duplicate universe parameters in $data" }
                // (3): "the declaration's type is actually a type and not a value (that infer declar.ty returns an expression Sort <n>)"
//                println("found type: ${data.typeExpr.toStringDetailed()}")
                val declaredTypeSortLevel = data.typeExpr.inferSort()

                val debugStart = env.clock.elapsedNow()
                when (data) {
                    is Declaration.Axiom -> {} // no extra checks needed
                    is Declaration.Def -> {
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for ${data.name.toStringDetailed()} $data"
                        }
                    }

                    is Declaration.Opaque -> {
                        // TODO: treat opqaue differently
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for ${data.name.toStringDetailed()} $data"
                        }
                    }

                    is Declaration.Quot -> {} // no extra checks needed
                    is Declaration.Thm -> {
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for ${data.name.toStringDetailed()} $data"
                        }
                        check(declaredTypeSortLevel.isLessOrEqual(Level.Zero)) {
                            "The type of a theorem has to be a proposition: found ${data.typeExpr.toStringDetailed()}"
                        }
                    }
                }
                if (shouldTimeDeclaration) {
                    println("i: checked declaration at index=$index start=$debugStart end=${env.clock.elapsedNow()}")
                }

                env.declTypeByName[data.name] = data.typeExpr
                env.counter++

                // (4): "the declaration's type has no free variables"
                // TODO
            }

            is Inductive -> checkInductive(data)

            is Meta -> {} // no-op
        }
        if (env.shouldLog) {
            println(
                "stats: defEqCalls=${env.defEqCalls} defEqCacheHits=${env.defEqCacheHits} " +
                        "defEqInProgressSkips=${env.defEqInProgressSkips} defEqCacheSize=${env.defEqCache.size}"
            )
        }
        if (data is Declaration || data is Inductive) {
            env.clearCustom()
        }
        if (env.shouldLog) {
            println("ended: ${env.clock.elapsedNow()}")
        }
//        println("apple: ${env.levels.size} // ${env.expressions.size} // ${env.declarations.size} // ${env.names.size}")
    }
}

context(env: Environment)
fun typeCheckDeclaration(value: Expression, expectedType: Expression): Boolean {
    if (env.shouldLog) println("found value: ${value/*.toStringDetailed()*/}")
    return value.checkHasType(expectedType)
}

context(env: Environment)
private fun Expression.checkHasType(
    expectedType: Expression,
    localCtx: List<Expression> = emptyList(),
): Boolean {
    val expectedTypeWhnf = expectedType.whnf(localCtx = localCtx)
    if (this is Expression.Lam && expectedTypeWhnf is Expression.ForallE) {
        val _ = this.typeExpr.inferSort(localCtx = localCtx)
        if (!this.typeExpr.isDefEq(expectedTypeWhnf.typeExpr, localCtx, localCtx)) {
            return false
        }
        return this.bodyExpr.checkHasType(
            expectedTypeWhnf.bodyExpr,
            listOf(this.typeExpr) + localCtx,
        )
    }

    val inferredValueType = this.inferType(localCtx = localCtx)
    if (env.shouldLog) println("inferred type of value: ${inferredValueType/*.toStringDetailed()*/}")
    return expectedType.isDefEq(inferredValueType, localCtx, localCtx)
}

context(env: Environment)
fun Expression.isDefEq(
    other: Expression,
    localCtxLeft: List<Expression> = emptyList(),
    localCtxRight: List<Expression> = emptyList(),
): Boolean {
    val leftExpr = this
    val rightExpr = other
    env.defEqCalls += 1

    val leftCtxId = env.localCtxId(localCtxLeft)
    val rightCtxId = env.localCtxId(localCtxRight)
    val cacheKey = if (
        leftExpr.ie < rightExpr.ie ||
        (leftExpr.ie == rightExpr.ie && leftCtxId <= rightCtxId)
    ) {
        DefEqCacheKey(leftExpr.ie, rightExpr.ie, leftCtxId, rightCtxId)
    } else {
        DefEqCacheKey(rightExpr.ie, leftExpr.ie, rightCtxId, leftCtxId)
    }

    env.defEqCache[cacheKey]?.let { cachedResult ->
        env.defEqCacheHits += 1
        return cachedResult
    }
    if (!env.defEqInProgress.add(cacheKey)) {
        env.defEqInProgressSkips += 1
        return env.defEqCycleAssumptionDepth > 0
    }

    val result = try {
        if (leftExpr == rightExpr) {
            true
        } else if (
            (leftExpr is Expression.Lam || rightExpr is Expression.Lam) &&
            leftExpr.tryProofIrrelevanceDefEq(rightExpr, localCtxLeft, localCtxRight)
        ) {
            true
        } else {
            val lazyDeltaEq = leftExpr.tryLazyDeltaDefEq(rightExpr, localCtxLeft, localCtxRight)
            if (lazyDeltaEq != null) {
                lazyDeltaEq
            } else {
                val sameShape = leftExpr.sameShape(rightExpr)
                if (sameShape) {
                    true
                } else {
                    val leftWhnfExpr =
                        if (leftExpr.isWhnfByShape()) leftExpr else leftExpr.whnf(localCtx = localCtxLeft)
                    val rightWhnfExpr =
                        if (rightExpr.isWhnfByShape()) rightExpr else rightExpr.whnf(localCtx = localCtxRight)
                    if (leftWhnfExpr == rightWhnfExpr) {
                        true
                    } else if (leftWhnfExpr.isDefEqWhnf(rightWhnfExpr, localCtxLeft, localCtxRight)) {
                        true
                    } else {
                        val tempLog = env.shouldLog
                        env.shouldLog = false
                        leftWhnfExpr.tryProofIrrelevanceDefEq(rightWhnfExpr, localCtxLeft, localCtxRight)
                            .also { env.shouldLog = tempLog }
                    }
                }
            }
        }
    } finally {
        env.defEqInProgress.remove(cacheKey)
    }

    env.defEqCache[cacheKey] = result
    return result
}

context(env: Environment)
private inline fun <T> withDefEqCycleAssumptions(block: () -> T): T {
    env.defEqCycleAssumptionDepth += 1
    return try {
        block()
    } finally {
        env.defEqCycleAssumptionDepth -= 1
    }
}

private enum class LazyDeltaStepKind(val priority: Int) {
    Regular(1),
    Abbrev(2),
    Forced(3),
}

private data class LazyDeltaStep(
    val unfoldedExpr: Expression,
    val kind: LazyDeltaStepKind,
    val regularHeight: Int = 0,
)

private enum class LazyDeltaChoice {
    Left,
    Right,
    Both,
}

context(env: Environment)
private fun Expression.matchesLazyDeltaHeadOf(other: Expression): Boolean {
    val thisHead = this.asAppSpine().first
    val otherHead = other.asAppSpine().first
    return when {
        thisHead == otherHead -> true
        thisHead is Expression.Const && otherHead is Expression.Const ->
            thisHead.name == otherHead.name &&
                    thisHead.levels.size == otherHead.levels.size &&
                    (thisHead.levels == otherHead.levels ||
                            thisHead.levels.zip(otherHead.levels).all { [l1, l2] -> l1.isEqual(l2) })

        else -> false
    }
}

context(env: Environment)
private fun Expression.reachesLazyDeltaHeadOf(
    other: Expression,
    localCtx: List<Expression>,
): Boolean {
    var current = this
    val seen = mutableSetOf<Int>()
    while (true) {
        if (current.matchesLazyDeltaHeadOf(other)) return true
        if (!seen.add(current.ie)) return false
        val next = current.tryLazyDeltaStep(localCtx)?.unfoldedExpr ?: return false
        if (next == current) return false
        current = next
    }
}

context(env: Environment)
private fun Expression.tryLazyDeltaDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftSpine = this.asAppSpine()
    val rightSpine = other.asAppSpine()
    this.trySameHeadConstCongruence(other, localCtxLeft, localCtxRight)?.let { return it }
    if (!this.shouldTryLazyDeltaWith(other)) return null

    val leftStep = this.tryLazyDeltaStep(localCtxLeft)
    val rightStep = other.tryLazyDeltaStep(localCtxRight)
    val choice = when {
        leftStep?.unfoldedExpr?.reachesLazyDeltaHeadOf(other, localCtxLeft) == true &&
                rightStep?.unfoldedExpr?.reachesLazyDeltaHeadOf(this, localCtxRight) != true -> LazyDeltaChoice.Left

        rightStep?.unfoldedExpr?.reachesLazyDeltaHeadOf(this, localCtxRight) == true &&
                leftStep?.unfoldedExpr?.reachesLazyDeltaHeadOf(other, localCtxLeft) != true -> LazyDeltaChoice.Right

        else -> chooseLazyDeltaSide(leftStep, rightStep)
    }
    return when (choice) {
        LazyDeltaChoice.Left ->
            true.takeIf { leftStep!!.unfoldedExpr.isDefEq(other, localCtxLeft, localCtxRight) }

        LazyDeltaChoice.Right ->
            true.takeIf { this.isDefEq(rightStep!!.unfoldedExpr, localCtxLeft, localCtxRight) }

        LazyDeltaChoice.Both ->
            true.takeIf { leftStep!!.unfoldedExpr.isDefEq(rightStep!!.unfoldedExpr, localCtxLeft, localCtxRight) }

        null -> null
    }
}

context(env: Environment)
private fun Expression.shouldTryLazyDeltaWith(other: Expression): Boolean {
    val leftSpine = this.asAppSpine()
    val rightSpine = other.asAppSpine()
    val leftHead = leftSpine.first
    val rightHead = rightSpine.first
    val maxArity = maxOf(leftSpine.second.size, rightSpine.second.size)

    val sameHeadConst = leftHead is Expression.Const &&
            rightHead is Expression.Const &&
            leftHead.name == rightHead.name
    if (sameHeadConst && maxArity >= 4) {
        return true
    }

    val hasReducibleHead = leftHead.lazyDeltaStepInfo() != null || rightHead.lazyDeltaStepInfo() != null
    return hasReducibleHead && maxArity >= 3
}

context(env: Environment)
private fun Expression.trySameHeadConstCongruence(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftSpine = this.asAppSpine()
    val rightSpine = other.asAppSpine()
    val leftConst = leftSpine.first as? Expression.Const ?: return null
    val rightConst = rightSpine.first as? Expression.Const ?: return null
    val leftArgs = leftSpine.second
    val rightArgs = rightSpine.second
    if (leftConst.name != rightConst.name) return null
    if (leftConst.decl is Inductive.RecursorVal || rightConst.decl is Inductive.RecursorVal) {
        return null
    }

    if (leftConst.levels.size != rightConst.levels.size) {
        return null
    }
    if (leftArgs.size != rightArgs.size) {
        return null
    }
    if (
        this.isFullyAppliedSingleCtorStructureConstructor(leftSpine, leftConst, leftArgs) &&
        other.isFullyAppliedSingleCtorStructureConstructor(rightSpine, rightConst, rightArgs)
    ) {
        return null
    }
    val congruenceMismatchIsDecisive =
        leftConst.lazyDeltaStepInfo() == null && rightConst.lazyDeltaStepInfo() == null
    val levelsMatch = leftConst.levels == rightConst.levels ||
            leftConst.levels.zip(rightConst.levels).all { levelPair ->
                levelPair.first.isEqual(levelPair.second)
            }
    if (!levelsMatch) return null
    compareAppArgumentsWithKnownFunctionTypes(
        leftConst,
        leftArgs,
        rightConst,
        rightArgs,
        localCtxLeft,
        localCtxRight,
        definitiveMismatch = congruenceMismatchIsDecisive,
    )?.let { return true }
    if (!congruenceMismatchIsDecisive) return null

    for (index in leftArgs.lastIndex downTo 0) {
        if (!leftArgs[index].isDefEq(rightArgs[index], localCtxLeft, localCtxRight)) {
            return false.takeIf { congruenceMismatchIsDecisive }
        }
    }
    return true
}

context(env: Environment)
private fun Expression.hasTheoremOrOpaqueHead(): Boolean {
    val headConst = this.asAppSpine().first as? Expression.Const ?: return false
    return when (headConst.decl) {
        is Declaration.Opaque, is Declaration.Thm -> true
        else -> false
    }
}

context(env: Environment)
private fun Expression.App.isDefEqWhnfSpine(
    other: Expression.App,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val leftSpine = this.unfoldApp()
    val rightSpine = other.unfoldApp()
    val leftArgs = leftSpine.second
    val rightArgs = rightSpine.second
    if (leftArgs.size != rightArgs.size) {
        return this.fnExpr.isDefEq(other.fnExpr, localCtxLeft, localCtxRight) &&
                this.argExpr.isDefEq(other.argExpr, localCtxLeft, localCtxRight)
    }
    if (!leftSpine.first.isDefEq(rightSpine.first, localCtxLeft, localCtxRight)) {
        return false
    }
    compareAppArgumentsWithKnownFunctionTypes(
        leftSpine.first,
        leftArgs,
        rightSpine.first,
        rightArgs,
        localCtxLeft,
        localCtxRight,
    )?.let { return true }
    for (index in leftArgs.lastIndex downTo 0) {
        if (!leftArgs[index].isDefEq(rightArgs[index], localCtxLeft, localCtxRight)) {
            return false
        }
    }
    return true
}

context(env: Environment)
private fun compareAppArgumentsWithKnownFunctionTypes(
    leftHead: Expression,
    leftArgs: List<Expression>,
    rightHead: Expression,
    rightArgs: List<Expression>,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
    definitiveMismatch: Boolean = false,
): Boolean? {
    if (leftArgs.size != rightArgs.size) return null
    var leftFnType = leftHead.inferType(localCtx = localCtxLeft)
    var rightFnType = rightHead.inferType(localCtx = localCtxRight)
    for (index in leftArgs.indices) {
        val leftBinder = leftFnType.whnf(localCtx = localCtxLeft) as? Expression.ForallE ?: return null
        val rightBinder = rightFnType.whnf(localCtx = localCtxRight) as? Expression.ForallE ?: return null
        val leftArg = leftArgs[index]
        val rightArg = rightArgs[index]

        val domainsAreProps =
            leftBinder.typeExpr.inferSort(localCtx = localCtxLeft).isLessOrEqual(Level.Zero) &&
                    rightBinder.typeExpr.inferSort(localCtx = localCtxRight).isLessOrEqual(Level.Zero)
        val argsMatch = when {
            leftArg == rightArg -> true

            domainsAreProps &&
                    leftBinder.typeExpr.isDefEq(rightBinder.typeExpr, localCtxLeft, localCtxRight) -> true

            else -> leftArg.isDefEq(rightArg, localCtxLeft, localCtxRight)
        }
        if (!argsMatch) {
            return false.takeIf { definitiveMismatch }
        }

        leftFnType = leftBinder.bodyExpr.applySubst(listOf(leftArg))
        rightFnType = rightBinder.bodyExpr.applySubst(listOf(rightArg))
    }
    return true
}

context(env: Environment)
private fun Expression.isFullyAppliedSingleCtorStructureConstructor(
    spine: Pair<Expression, List<Expression>> = this.asAppSpine(),
    headConst: Expression.Const? = spine.first as? Expression.Const,
    args: List<Expression> = spine.second,
): Boolean {
    val ctorDecl = headConst?.decl as? Inductive.ConstructorVal ?: return false
    if (args.size != ctorDecl.numParams + ctorDecl.numFields) return false
    val inductiveIndex = env.nameIndices[ctorDecl.inductName] ?: return false
    val inductiveDecl = env.declarations[inductiveIndex] as? Inductive.InductiveVal ?: return false
    return !inductiveDecl.isRec && inductiveDecl.ctors.size == 1 && inductiveDecl.numIndices == 0
}

context(env: Environment)
private fun Expression.Const.projectionReductionInfo(): ProjectionReductionInfo? {
    val nameIndex = env.nameIndices[this.name] ?: return null
    env.projectionReductionInfoByNameIndex[nameIndex]?.let { return it }

    val result = run {
        val defDecl = this.decl as? Declaration.Def ?: return@run null
        var binderCount = 0
        var projectionBody: Expression = defDecl.valueExpr
        while (true) {
            projectionBody = when (projectionBody) {
                is Expression.Mdata -> projectionBody.expr
                is Expression.LetE -> projectionBody.bodyExpr.applySubst(listOf(projectionBody.valueExpr))
                else -> break
            }
        }
        while (projectionBody is Expression.Lam) {
            binderCount += 1
            projectionBody = projectionBody.bodyExpr
            while (true) {
                projectionBody = when (projectionBody) {
                    is Expression.Mdata -> projectionBody.expr
                    is Expression.LetE -> projectionBody.bodyExpr.applySubst(listOf(projectionBody.valueExpr))
                    else -> break
                }
            }
        }

        val projectionExpr = projectionBody as? Expression.Proj ?: return@run null
        val structBvar = projectionExpr.structExpr as? Expression.Bvar ?: return@run null
        val structArgIndex = binderCount - 1 - structBvar.bvar
        if (structArgIndex !in 0 until binderCount) return@run null

        ProjectionReductionInfo(
            inductiveNameIndex = projectionExpr.typeNameIndex,
            fieldIndex = projectionExpr.projIndex,
            arity = binderCount,
            structArgIndex = structArgIndex,
        )
    }

    env.projectionReductionInfoByNameIndex[nameIndex] = result
    return result
}

context(env: Environment)
private fun Expression.App.tryReduceProjectionApp(): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val headConst = headExpr as? Expression.Const ?: return null
    val projectionInfo = headConst.projectionReductionInfo() ?: return null
    if (args.size < projectionInfo.arity) return null

    val projectionExpr = env.addCustomExpr {
        Expression.Proj(
            typeName = projectionInfo.inductiveNameIndex,
            idx = projectionInfo.fieldIndex,
            struct = args[projectionInfo.structArgIndex].ie,
            ie = it,
        )
    }
    return projectionExpr.applyArgs(args.drop(projectionInfo.arity))
}

private fun chooseLazyDeltaSide(left: LazyDeltaStep?, right: LazyDeltaStep?): LazyDeltaChoice? {
    if (left == null && right == null) return null
    if (left != null && right == null) return LazyDeltaChoice.Left
    if (left == null && right != null) return LazyDeltaChoice.Right

    val kindCmp = left!!.kind.priority.compareTo(right!!.kind.priority)
    if (kindCmp > 0) return LazyDeltaChoice.Left
    if (kindCmp < 0) return LazyDeltaChoice.Right

    val heightCmp = left.regularHeight.compareTo(right.regularHeight)
    if (heightCmp > 0) return LazyDeltaChoice.Left
    if (heightCmp < 0) return LazyDeltaChoice.Right
    return LazyDeltaChoice.Both
}

context(env: Environment)
private fun Expression.tryLazyDeltaStep(localCtx: List<Expression>): LazyDeltaStep? {
    val headExpr = this.asAppSpine().first
    val headStep = when (headExpr) {
        is Expression.Proj -> LazyDeltaHeadInfo(LazyDeltaStepKind.Forced)
        else -> headExpr.lazyDeltaStepInfo()
    } ?: return null
    val unfoldedExpr = this.unfoldLazyDeltaHeadToFixpoint(localCtx) ?: return null

    return LazyDeltaStep(
        unfoldedExpr = unfoldedExpr,
        kind = headStep.kind,
        regularHeight = headStep.regularHeight,
    )
}

context(env: Environment)
private fun Expression.unfoldLazyDeltaHeadToFixpoint(localCtx: List<Expression>): Expression? {
    var current = this
    var changed = false
    val seen = mutableSetOf<Int>()
    while (true) {
        if (!seen.add(current.ie)) {
            return current.takeIf { changed }
        }
        val headExpr = current.asAppSpine().first
        val next = when (headExpr) {
            is Expression.Proj -> current.tryWhnfStep(localCtx)
            else -> if (headExpr.lazyDeltaStepInfo() != null) current.tryUnfoldSpineHeadOnce() else null
        } ?: return current.takeIf { changed }
        if (next == current) return current.takeIf { changed }
        current = next
        changed = true
    }
}

context(env: Environment)
private fun Expression.tryUnfoldSpineHeadOnce(): Expression? = when (this) {
    is Expression.App -> {
        this.tryReduceProjectionApp()?.let { return it }
        val projectionHead = this.unfoldApp().first as? Expression.Const
        if (projectionHead?.projectionReductionInfo() != null) return null

        val spine = this.unfoldApp()
        val originalHead = spine.first
        val originalArgs = spine.second

        var currentHead = when (originalHead) {
            is Expression.Const -> originalHead.tryUnfoldReducibleHeadOnce() ?: return null
            else -> originalHead
        }
        val remainingArgs = originalArgs.toMutableList()
        var changed = currentHead != originalHead

        while (true) {
            when (currentHead) {
                is Expression.Lam -> {
                    if (remainingArgs.isEmpty()) break
                    currentHead = currentHead.bodyExpr.applySubst(listOf(remainingArgs.removeAt(0)))
                    changed = true
                }

                is Expression.LetE -> {
                    currentHead = currentHead.bodyExpr.applySubst(listOf(currentHead.valueExpr))
                    changed = true
                }

                is Expression.Mdata -> {
                    currentHead = currentHead.expr
                    changed = true
                }

                else -> break
            }
        }
        if (!changed) return null
        currentHead.applyArgs(remainingArgs)
    }

    else -> this.tryUnfoldReducibleHeadOnce()
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

private data class LazyDeltaHeadInfo(
    val kind: LazyDeltaStepKind,
    val regularHeight: Int = 0,
)

context(env: Environment)
private fun Expression.lazyDeltaStepInfo(): LazyDeltaHeadInfo? = when (this) {
    is Expression.Const -> {
        val defDecl = this.decl as? Declaration.Def ?: return null
        when (val hints = defDecl.hints) {
            Declaration.Def.Hints.Opaque -> null
            Declaration.Def.Hints.Abbrev -> LazyDeltaHeadInfo(LazyDeltaStepKind.Abbrev)
            is Declaration.Def.Hints.Regular -> LazyDeltaHeadInfo(LazyDeltaStepKind.Regular, hints.value)
        }
    }

    is Expression.Lam, is Expression.LetE, is Expression.Mdata -> LazyDeltaHeadInfo(LazyDeltaStepKind.Forced)
    else -> null
}

context(env: Environment)
private fun Expression.asAppSpine(): Pair<Expression, List<Expression>> = when (this) {
    is Expression.App -> this.unfoldApp()
    else -> this to emptyList()
}

context(env: Environment)
private fun Expression.isWhnfByShape(): Boolean = when (this) {
    is Expression.Bvar,
    is Expression.ForallE,
    is Expression.Lam,
    is Expression.NatVal,
    is Expression.Sort,
    is Expression.StrVal -> true

    is Expression.Const -> this.decl !is Declaration.Def || this.projectionReductionInfo() != null

    is Expression.App,
    is Expression.LetE,
    is Expression.Mdata,
    is Expression.Proj -> false
}

context(env: Environment)
private fun Expression.sameShape(other: Expression): Boolean = when (this) {
    else -> {
        val leftId = this.ie
        val rightId = other.ie
        val cacheKey = if (leftId <= rightId) {
            (leftId.toLong() shl 32) xor (rightId.toLong() and 0xffffffffL)
        } else {
            (rightId.toLong() shl 32) xor (leftId.toLong() and 0xffffffffL)
        }
        env.sameShapeCache[cacheKey]?.let { return it }

        val result = when {
            leftId == rightId -> true
            this is Expression.Bvar && other is Expression.Bvar -> this.bvar == other.bvar
            this is Expression.NatVal && other is Expression.NatVal -> this.natVal == other.natVal
            this is Expression.StrVal && other is Expression.StrVal -> this.strVal == other.strVal
            this is Expression.Sort && other is Expression.Sort -> this.level == other.level
            this is Expression.Const && other is Expression.Const ->
                this.name == other.name &&
                        this.levels.size == other.levels.size &&
                        this.levels.zip(other.levels).all { it.first == it.second }

            this is Expression.App && other is Expression.App ->
                this.fnExpr.sameShape(other.fnExpr) && this.argExpr.sameShape(other.argExpr)

            this is Expression.ForallE && other is Expression.ForallE ->
                this.typeExpr.sameShape(other.typeExpr) && this.bodyExpr.sameShape(other.bodyExpr)

            this is Expression.Lam && other is Expression.Lam ->
                this.typeExpr.sameShape(other.typeExpr) && this.bodyExpr.sameShape(other.bodyExpr)

            this is Expression.LetE && other is Expression.LetE ->
                this.typeExpr.sameShape(other.typeExpr) &&
                        this.valueExpr.sameShape(other.valueExpr) &&
                        this.bodyExpr.sameShape(other.bodyExpr)

            this is Expression.Mdata && other is Expression.Mdata ->
                this.expr.sameShape(other.expr)

            this is Expression.Proj && other is Expression.Proj ->
                this.typeNameExpr == other.typeNameExpr &&
                        this.projIndex == other.projIndex &&
                        this.structExpr.sameShape(other.structExpr)

            else -> false
        }
        env.sameShapeCache[cacheKey] = result
        result
    }
}

context(env: Environment)
private fun Expression.isDefEqWhnf(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean = when (this) {
    is Expression.App if other is Expression.App ->
        if (
            this.isFullyAppliedSingleCtorStructureConstructor() &&
            other.isFullyAppliedSingleCtorStructureConstructor()
        ) {
            this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight) ||
                    this.isDefEqWhnfSpine(other, localCtxLeft, localCtxRight)
        } else {
            this.isDefEqWhnfSpine(other, localCtxLeft, localCtxRight) ||
                    this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight)
        }

    is Expression.Bvar if other is Expression.Bvar -> {
        if (this.bvar == other.bvar) {
            true
        } else if (this.bvar < localCtxLeft.size && other.bvar < localCtxRight.size) {
            val thisType = localCtxLeft[this.bvar].lift(this.bvar + 1)
            val otherType = localCtxRight[other.bvar].lift(other.bvar + 1)
            thisType.isDefEq(otherType, localCtxLeft, localCtxRight) ||
                    this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight)
        } else {
            false
        }
    }

    is Expression.Const if other is Expression.Const ->
        this.name == other.name &&
                this.levels.size == other.levels.size &&
                (this.levels == other.levels ||
                        this.levels.zip(other.levels).all { [l1, l2] -> l1.isEqual(l2) })

    is Expression.ForallE if other is Expression.ForallE -> {
        this.typeExpr.isDefEq(other.typeExpr, localCtxLeft, localCtxRight) &&
                this.bodyExpr.isDefEq(
                    other.bodyExpr,
                    listOf(this.typeExpr) + localCtxLeft,
                    listOf(other.typeExpr) + localCtxRight,
                )
    }

    is Expression.Lam if other is Expression.Lam -> {
        this.typeExpr.isDefEq(other.typeExpr, localCtxLeft, localCtxRight) &&
                this.bodyExpr.isDefEq(
                    other.bodyExpr,
                    listOf(this.typeExpr) + localCtxLeft,
                    listOf(other.typeExpr) + localCtxRight,
                )
    }

    is Expression.Lam ->
        this.tryEtaReduce()?.isDefEq(other, localCtxLeft, localCtxRight)
            ?: this.tryCompareWithFunction(other, localCtxLeft, localCtxRight)
            ?: false

    is Expression.LetE if other is Expression.LetE -> TODO()
    is Expression.Mdata if other is Expression.Mdata -> TODO()
    is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
    is Expression.NatVal if other.isNatZeroCtorConst() -> this.natVal.isZero()

    is Expression.Const if this.isNatZeroCtorConst() && other is Expression.NatVal -> other.natVal.isZero()
    is Expression.Proj if other is Expression.Proj ->
        this.typeNameExpr == other.typeNameExpr &&
                this.projIndex == other.projIndex &&
                this.structExpr.isDefEq(other.structExpr, localCtxLeft, localCtxRight)

    is Expression.Sort if other is Expression.Sort -> this.level.isEqual(other.level)

    is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
    else -> {
        if (other is Expression.Lam) {
            other.tryEtaReduce()?.let {
                return this.isDefEq(it, localCtxLeft, localCtxRight)
            }
            this.tryCompareWithFunction(other, localCtxLeft, localCtxRight)?.let {
                return it
            }
        }
        if (
            this.canBeStructureLikeValue() &&
            other.canBeStructureLikeValue() &&
            this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight)
        ) {
            return true
        }
        val reducedThis = this.reduce(localCtx = localCtxLeft)
        val reducedOther = other.reduce(localCtx = localCtxRight)
        if (reducedThis == this && reducedOther == other) {
            false
        } else {
            reducedThis.isDefEq(reducedOther, localCtxLeft, localCtxRight)
        }
    }
}

context(env: Environment)
private fun Expression.tryCompareWithFunction(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftLam = this as? Expression.Lam
    val rightLam = other as? Expression.Lam
    if ((leftLam == null) == (rightLam == null)) return null

    val leftDomain = if (leftLam != null) {
        leftLam.typeExpr
    } else {
        (this.inferType(localCtx = localCtxLeft).reduce(localCtx = localCtxLeft) as? Expression.ForallE)?.typeExpr
            ?: return null
    }
    val rightDomain = if (rightLam != null) {
        rightLam.typeExpr
    } else {
        (other.inferType(localCtx = localCtxRight).reduce(localCtx = localCtxRight) as? Expression.ForallE)?.typeExpr
            ?: return null
    }
    if (!leftDomain.isDefEq(rightDomain, localCtxLeft, localCtxRight)) return null

    val binderExpr = env.addCustomExpr { Expression.Bvar(0, it) }
    val leftUnderBinder = if (leftLam != null) {
        leftLam.bodyExpr
    } else {
        val liftedLeft = this.lift(1)
        env.addCustomExpr { Expression.App(liftedLeft.ie, binderExpr.ie, it) }
    }
    val rightUnderBinder = if (rightLam != null) {
        rightLam.bodyExpr
    } else {
        val liftedRight = other.lift(1)
        env.addCustomExpr { Expression.App(liftedRight.ie, binderExpr.ie, it) }
    }
    return withDefEqCycleAssumptions {
        leftUnderBinder.isDefEq(
            rightUnderBinder,
            listOf(leftDomain) + localCtxLeft,
            listOf(rightDomain) + localCtxRight,
        )
    }
}

context(env: Environment)
private fun Expression.tryCompareWithKnownFunctionType(
    other: Expression,
    leftDomain: Expression,
    rightDomain: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftReduced = this.whnf(localCtx = localCtxLeft)
    val rightReduced = other.whnf(localCtx = localCtxRight)
    val leftLam = leftReduced as? Expression.Lam
    val rightLam = rightReduced as? Expression.Lam
    if (leftLam == null && rightLam == null) return null
    if (!leftDomain.isDefEq(rightDomain, localCtxLeft, localCtxRight)) return null

    val binderExpr = env.addCustomExpr { Expression.Bvar(0, it) }
    val leftUnderBinder = if (leftLam != null) {
        leftLam.bodyExpr
    } else {
        val liftedLeft = leftReduced.lift(1)
        env.addCustomExpr { Expression.App(liftedLeft.ie, binderExpr.ie, it) }
    }
    val rightUnderBinder = if (rightLam != null) {
        rightLam.bodyExpr
    } else {
        val liftedRight = rightReduced.lift(1)
        env.addCustomExpr { Expression.App(liftedRight.ie, binderExpr.ie, it) }
    }
    return leftUnderBinder.isDefEq(
        rightUnderBinder,
        listOf(leftDomain) + localCtxLeft,
        listOf(rightDomain) + localCtxRight,
    )
}

private fun Expression.canBeStructureLikeValue(): Boolean = when (this) {
    is Expression.App,
    is Expression.Bvar,
    is Expression.Const,
    is Expression.LetE,
    is Expression.Mdata,
    is Expression.Proj,
    is Expression.StrVal -> true

    else -> false
}

context(env: Environment)
private fun Expression.tryStringLitCtor(): Expression? {
    val stringLiteral = this as? Expression.StrVal ?: return null
    val ctorExpr = stringLiteral.toStringOfListExpr().whnf()
    val [headExpr, _] = ctorExpr.unfoldApp()
    val headCtorDecl = (headExpr as? Expression.Const)?.decl as? Inductive.ConstructorVal
    return ctorExpr.takeIf { headCtorDecl != null }
}

context(env: Environment)
private fun Expression.StrVal.toStringOfListExpr(): Expression {
    val stringInfo = env.findRootInductive("String")
        ?: error("String literal used without String inductive in environment")
    val stringOfListIndex = env.findChildNameIndex(stringInfo.first, "ofList")
        ?: error("String literal used without String.ofList declaration in environment")
    val stringOfListExpr = env.addCustomExpr {
        Expression.Const(_name = stringOfListIndex, us = emptyList(), ie = it)
    }
    return stringOfListExpr.applyArgs(listOf(this.toListCharExpr()))
}

context(env: Environment)
private fun Expression.StrVal.toListCharExpr(): Expression {
    val charTypeIndex = env.findRootInductive("Char")?.first
        ?: error("String literal used without Char inductive in environment")
    val listInfo = env.findRootInductive("List")
        ?: error("String literal used without List inductive in environment")
    val charOfNatNameIndex = env.findChildNameIndex(charTypeIndex, "ofNat")
        ?: error("String literal used without Char.ofNat declaration in environment")

    val charTypeExpr = env.addCustomExpr {
        Expression.Const(_name = charTypeIndex, us = emptyList(), ie = it)
    }
    val charOfNatExpr = env.addCustomExpr {
        Expression.Const(_name = charOfNatNameIndex, us = emptyList(), ie = it)
    }

    val listCtorDecls = listInfo.second.ctors.map { ctorIndex ->
        env.declarations[ctorIndex] as? Inductive.ConstructorVal
            ?: error("List constructor declaration $ctorIndex not found")
    }
    val listNilCtorIndex = listCtorDecls.singleOrNull { it.numFields == 0 }?.let { ctorDecl ->
        env.nameIndices[ctorDecl.name]
    } ?: error("List.nil constructor not found")
    val listConsCtorIndex = listCtorDecls.singleOrNull { it.numFields == 2 }?.let { ctorDecl ->
        env.nameIndices[ctorDecl.name]
    } ?: error("List.cons constructor not found")

    val listNilExpr = env.addCustomExpr {
        Expression.Const(_name = listNilCtorIndex, us = listOf(Level.Zero.il), ie = it)
    }
    val listConsExpr = env.addCustomExpr {
        Expression.Const(_name = listConsCtorIndex, us = listOf(Level.Zero.il), ie = it)
    }
    var listExpr = listNilExpr.applyArgs(listOf(charTypeExpr))
    for (codePoint in this.strVal.toUnicodeScalarValues().asReversed()) {
        val natExpr = env.addCustomExpr {
            Expression.NatVal(NatValue.fromString(codePoint.toString()), it)
        }
        val charExpr = charOfNatExpr.applyArgs(listOf(natExpr))
        listExpr = listConsExpr.applyArgs(listOf(charTypeExpr, charExpr, listExpr))
    }
    return listExpr
}

// Kotlin strings are UTF-16; Lean Char.ofNat expects Unicode scalar values.
private fun String.toUnicodeScalarValues(): List<Int> {
    val result = mutableListOf<Int>()
    var index = 0
    while (index < this.length) {
        val current = this[index]
        if (current in Char.MIN_HIGH_SURROGATE..Char.MAX_HIGH_SURROGATE && index + 1 < this.length) {
            val next = this[index + 1]
            if (next in Char.MIN_LOW_SURROGATE..Char.MAX_LOW_SURROGATE) {
                result += (Char.MAX_VALUE.code + 1) +
                        ((current - Char.MIN_HIGH_SURROGATE) shl 10) + (next - Char.MIN_LOW_SURROGATE)
                index += 2
                continue
            }
        }
        result += current.code
        index++
    }
    return result
}

context(env: Environment)
private fun Expression.isNatZeroCtorConst(): Boolean {
    val constExpr = this as? Expression.Const ?: return false
    val ctorDecl = constExpr.decl as? Inductive.ConstructorVal ?: return false
    if (ctorDecl.numParams != 0 || ctorDecl.numFields != 0) return false
    val inductiveName = ctorDecl.inductName as? Name.Str ?: return false
    return inductiveName.pre == 0 && inductiveName.str == "Nat"
}

context(env: Environment)
private fun Expression.inferTypeAfterZetaLets(
    pendingSubst: List<Expression>,
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
): Expression {
    var currentExpr: Expression = this
    var currentSubst = pendingSubst
    while (currentExpr is Expression.LetE) {
        val letExpr = currentExpr
        val letTypeExpr = if (currentSubst.isEmpty()) {
            letExpr.typeExpr
        } else {
            letExpr.typeExpr.applySubst(currentSubst)
        }
        val _ = letTypeExpr.inferSort(levelSubst, localCtx)

        val rawValueExpr = letExpr.valueExpr
        val letValueExpr = if (currentSubst.isEmpty()) {
            rawValueExpr
        } else {
            rawValueExpr.applySubst(currentSubst)
        }
        val expectedTypeExpr = letTypeExpr.instantiateLevelParams(levelSubst)
        check(letValueExpr.checkHasType(expectedTypeExpr, localCtx)) {
            "Let value type mismatch in ${letExpr.toStringDetailed()}: expected ${expectedTypeExpr.toStringDetailed()}"
        }

        currentSubst = listOf(letValueExpr) + currentSubst
        currentExpr = letExpr.bodyExpr
    }

    val instantiatedExpr = if (currentSubst.isEmpty()) currentExpr else currentExpr.applySubst(currentSubst)
    return instantiatedExpr.inferType(levelSubst, localCtx)
}

context(env: Environment)
fun Expression.inferType(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList()
): Expression {
    val cacheKey = if (levelSubst.isEmpty()) {
        InferTypeCacheKey(this.ie, env.localCtxId(localCtx))
    } else {
        null
    }
    if (cacheKey != null) {
        env.inferTypeCacheNoLevelSubst[cacheKey]?.let { cachedType ->
            env.inferTypeCacheHits += 1
            return cachedType
        }
    }

    val ownsInProgressSlot = cacheKey != null && env.inferTypeInProgress.add(cacheKey)
    val result = try {
        when (this) {
//        is Expression.App -> {
//            val fnTy0 = this.fnExpr.inferType(levelSubst, localCtx)
//            val fnTy = fnTy0.reduce(levelSubst)
//            check(fnTy is Expression.ForallE) {
//                "Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}"
//            }
//
//            val arg = this.argExpr.instantiateLevelParams(levelSubst)
//            fnTy.bodyExpr
//                .applySubst(listOf(arg))
//                .instantiateLevelParams(levelSubst)
//                .reduce(levelSubst)
//        }
            is Expression.App -> {
                val fnTy0 = this.fnExpr.inferType(levelSubst, localCtx)
                val fnTy = fnTy0.whnf(localCtx = localCtx)
                check(fnTy is Expression.ForallE) {
                    "Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}"
                }
                val arg = this.argExpr.instantiateLevelParams(levelSubst)
                // TODO: this breaks in init-prelude
//            check(expectedArgTy.isDefEq(argTy, emptyMap(), argTy0.levelSubst, localCtx, localCtx)) {
//                "Application argument type mismatch in ${this.toStringDetailed()}: expected ${expectedArgTy.toStringDetailed()}, got ${argTy.toStringDetailed()}"
//            }
                fnTy.bodyExpr.applySubst(listOf(arg))
            }

            is Expression.Bvar -> {
                if (this.bvar < localCtx.size) {
                    // live binder: its stored type was recorded outside this binder,
                    // so lift it back under the current live-binder depth.
                    localCtx[this.bvar].lift(this.bvar + 1).instantiateLevelParams(levelSubst)
                } else {
                    error("Unbound bvar ${this.bvar} in ${this.toStringDetailed()}")
                }
            }

            is Expression.Const -> {
                val ty = env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
                ty.instantiateLevelParams(this.composeLevelSubst(levelSubst))
            }

            is Expression.ForallE -> {
                val left = this.typeExpr.inferSort(levelSubst, localCtx)
//            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")

                val right = this.bodyExpr.inferSort(levelSubst, listOf(this.typeExpr) + localCtx)

                val newLevel = env.addCustomImaxLevel(left.il, right.il)
                env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            }

            is Expression.Lam -> {
                val _ = this.typeExpr.inferSort(levelSubst, localCtx)
//            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")
                val bodyTyWhnf = this.bodyExpr.inferType(levelSubst, listOf(this.typeExpr) + localCtx)
                env.addCustomExpr {
                    this.copyAsForAllE().copy(body = bodyTyWhnf.ie, ie = it)
                }
            }

            is Expression.Sort -> {
                val normalizedLevel = this.level.instantiateLevelParams(levelSubst)
                val newLevel = env.addCustomSuccLevel(normalizedLevel.il)
                env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            }

            is Expression.LetE -> {
                // We just need to check that the type is a sort (do we?), we don't need the exact level (potential optimization?)
                val _ = this.typeExpr.inferSort(levelSubst, localCtx)

                val expectedTypeExpr = this.typeExpr.instantiateLevelParams(levelSubst)
                check(this.valueExpr.checkHasType(expectedTypeExpr, localCtx)) {
                    "Let value type mismatch in ${this.toStringDetailed()}: expected ${expectedTypeExpr.toStringDetailed()}"
                }

                this.bodyExpr.inferTypeAfterZetaLets(listOf(this.valueExpr), levelSubst, localCtx)
            }

            is Expression.Mdata -> TODO()
            is Expression.NatVal -> {
                val natInfo = env.findRootInductive("Nat")
                    ?: error("Nat literal ${this.natVal} used without Nat inductive in environment")
                val natTypeIndex = natInfo.first
                env.addCustomExpr {
                    Expression.Const(_name = natTypeIndex, us = emptyList(), ie = it)
                }
            }

            is Expression.Proj -> this.inferProjectionType(levelSubst, localCtx)
            is Expression.StrVal -> {
                val stringInfo = env.findRootInductive("String")
                    ?: error("String literal used without String inductive in environment")
                val stringTypeIndex = stringInfo.first
                env.addCustomExpr {
                    Expression.Const(_name = stringTypeIndex, us = emptyList(), ie = it)
                }
            }
        }
    } finally {
        if (ownsInProgressSlot) {
            env.inferTypeInProgress.remove(cacheKey)
        }
    }

    if (cacheKey != null && ownsInProgressSlot) {
        env.inferTypeCacheNoLevelSubst[cacheKey] = result
    }
    return result
}

context(env: Environment)
fun Expression.reduce(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
): Expression {
    val cacheKey = if (levelSubst.isEmpty()) {
        if (localCtx.isEmpty()) {
            null
        } else {
            ReduceCacheKey(this.ie, env.localCtxId(localCtx))
        }
    } else {
        null
    }
    if (cacheKey == null && levelSubst.isEmpty()) {
        env.reduceCacheNoLevelSubst[this.ie]?.let { return it }
    } else if (cacheKey != null) {
        env.reduceCacheWithCtxNoLevelSubst[cacheKey]?.let { return it }
    }
    if (env.shouldLog) println("trying to reduce ${this}")
    val result = when (this) {
        is Expression.App -> {
            val projectionReducedExpr = (this.instantiateLevelParams(levelSubst) as? Expression.App)?.let { appExpr ->
                val projectionHead = appExpr.unfoldApp().first as? Expression.Const
                val projectionInfo = projectionHead?.projectionReductionInfo()
                when {
                    projectionInfo == null -> null
                    appExpr.unfoldApp().second.size < projectionInfo.arity -> appExpr
                    else -> appExpr.tryReduceProjectionApp()?.reduce(localCtx = localCtx)
                }
            }
            val natReducedExpr = this.tryReduceNatLiteral(levelSubst)
            val natPrimitiveArity = this.natLiteralPrimitiveArity()
            if (projectionReducedExpr != null) {
                projectionReducedExpr
            } else if (natReducedExpr != null) {
                natReducedExpr
            } else if (natPrimitiveArity != null) {
                val appExpr = this.instantiateLevelParams(levelSubst) as Expression.App
                if (appExpr.unfoldApp().second.size < natPrimitiveArity) {
                    appExpr
                } else {
                    val unfoldedApp = appExpr.tryUnfoldSpineHeadOnce()
                    if (unfoldedApp != null && unfoldedApp != appExpr) {
                        unfoldedApp.reduce(localCtx = localCtx)
                    } else {
                        appExpr
                    }
                }
            } else if (!this.fnExpr.canReduceAtHead()) {
                this.tryReduceRecursor(levelSubst, localCtx)
                    ?: this.tryReduceQuot(levelSubst, localCtx)
                    ?: this.instantiateLevelParams(levelSubst)
            } else {
                when (val fnWhnf = this.fnExpr.reduce(levelSubst, localCtx)) {
                    is Expression.Lam -> {
                        val argExpr = this.argExpr.instantiateLevelParams(levelSubst)
                        fnWhnf.bodyExpr.applySubst(listOf(argExpr)).reduce(localCtx = localCtx)
                    }

                    else -> {
                        val appExprPreInst: Expression.App = if (fnWhnf == this.fnExpr) {
                            this
                        } else {
                            env.addCustomExpr { this.copy(fn = fnWhnf.ie, ie = it) } as Expression.App
                        }
                        val reducedApp = appExprPreInst.tryReduceRecursor(levelSubst, localCtx)
                            ?: appExprPreInst.tryReduceQuot(levelSubst, localCtx)
                        if (reducedApp != null) {
                            reducedApp
                        } else {
                            if (fnWhnf != this.fnExpr) {
                                appExprPreInst.reduce(localCtx = localCtx)
                            } else {
                                appExprPreInst.instantiateLevelParams(levelSubst)
                            } // MEM: 200 MB
                        }
                    }
                }
            }
        }

        is Expression.Lam -> this.instantiateLevelParams(levelSubst)
        is Expression.Bvar -> this
        is Expression.Const -> {
            when (val d = decl) {
                is Declaration.Def -> {
                    if (this.isNatLiteralPrimitiveConst()) {
                        this.instantiateLevelParams(levelSubst)
                    } else {
                        val constLevelSubst = this.composeLevelSubst(levelSubst)
                        val instantiatedValue = d.valueExpr.instantiateLevelParams(constLevelSubst)
                        instantiatedValue.reduce(localCtx = localCtx)
                    }
                }

                else -> this.instantiateLevelParams(levelSubst)
            }
        }

        is Expression.ForallE -> this.instantiateLevelParams(levelSubst)
        is Expression.Sort -> this.instantiateLevelParams(levelSubst)
        is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr)).reduce(levelSubst, localCtx)
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> this

        is Expression.Proj -> {
            val reducedStructExpr = this.structExpr.reduce(levelSubst, localCtx)
            val structExpr = reducedStructExpr.tryStringLitCtor() ?: reducedStructExpr
            val [head, args] = structExpr.unfoldApp()
            val ctorConst = head as? Expression.Const
            val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
            if (
                ctorDecl != null &&
                ctorDecl.inductName == this.typeNameExpr &&
                this.projIndex in 0 until ctorDecl.numFields &&
                args.size == ctorDecl.numParams + ctorDecl.numFields
            ) {
                val fieldExpr = args[ctorDecl.numParams + this.projIndex]
                if (fieldExpr.isNatLiteralPrimitive()) fieldExpr else fieldExpr.reduce(localCtx = localCtx)
            } else if (structExpr == this.structExpr.instantiateLevelParams(levelSubst)) {
                this.instantiateLevelParams(levelSubst)
            } else {
                env.addCustomExpr {
                    Expression.Proj(
                        typeName = this.typeNameIndex,
                        idx = this.projIndex,
                        struct = structExpr.ie,
                        ie = it,
                    )
                }
            }
        }

        is Expression.StrVal -> this
    }
    if (cacheKey == null && levelSubst.isEmpty()) {
        env.reduceCacheNoLevelSubst[this.ie] = result
    } else if (cacheKey != null) {
        env.reduceCacheWithCtxNoLevelSubst[cacheKey] = result
    }
    return result
}

context(env: Environment)
fun Expression.whnf(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
): Expression {
    var current = this.instantiateLevelParams(levelSubst)
    while (true) {
        val next = current.tryWhnfStep(localCtx) ?: return current
        if (next == current) return current
        current = next
    }
}

context(env: Environment)
private fun Expression.tryWhnfStep(localCtx: List<Expression>): Expression? = when (this) {
    is Expression.App -> {
        val projectionHead = this.unfoldApp().first as? Expression.Const
        val projectionInfo = projectionHead?.projectionReductionInfo()
        if (projectionInfo != null) {
            if (this.unfoldApp().second.size < projectionInfo.arity) return null
            this.tryReduceProjectionApp()?.let { return it }
        }
        this.tryReduceNatLiteral(emptyMap())?.let { return it }
        if (this.natLiteralPrimitiveArity() != null) {
            if (this.unfoldApp().second.size < this.natLiteralPrimitiveArity()!!) return null
            this.tryUnfoldSpineHeadOnce()?.let { return it }
        }
        this.tryUnfoldSpineHeadOnce()?.let { return it }

        when (val fnWhnf = this.fnExpr.whnf(localCtx = localCtx)) {
            is Expression.Lam -> fnWhnf.bodyExpr.applySubst(listOf(this.argExpr))
            else -> {
                val appExpr = if (fnWhnf == this.fnExpr) {
                    this
                } else {
                    env.addCustomExpr { this.copy(fn = fnWhnf.ie, ie = it) } as Expression.App
                }
                appExpr.tryReduceRecursorHead(emptyMap(), localCtx)
                    ?: appExpr.tryReduceQuotHead(emptyMap(), localCtx)
                    ?: appExpr.takeIf { it != this }
            }
        }
    }

    is Expression.Const -> if (this.isNatLiteralPrimitiveConst() || this.projectionReductionInfo() != null) {
        null
    } else {
        this.tryUnfoldReducibleHeadOnce()
    }
    is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr))
    is Expression.Mdata -> this.expr

    is Expression.Proj -> {
        val reducedStructExpr = this.structExpr.whnf(localCtx = localCtx)
        val structExpr = reducedStructExpr.tryStringLitCtor() ?: reducedStructExpr
        val [head, args] = structExpr.unfoldApp()
        val ctorConst = head as? Expression.Const
        val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
        if (
            ctorDecl != null &&
            ctorDecl.inductName == this.typeNameExpr &&
            this.projIndex in 0 until ctorDecl.numFields &&
            args.size == ctorDecl.numParams + ctorDecl.numFields
        ) {
            args[ctorDecl.numParams + this.projIndex]
        } else if (structExpr == this.structExpr) {
            null
        } else {
            env.addCustomExpr {
                Expression.Proj(
                    typeName = this.typeNameIndex,
                    idx = this.projIndex,
                    struct = structExpr.ie,
                    ie = it,
                )
            }
        }
    }

//    is Expression.StrVal -> this.tryStringLitCtor() ?: this

    else -> null
}

context(env: Environment)
private fun Expression.canReduceAtHead(): Boolean {
    return when (this) {
        is Expression.App -> this.fnExpr.canReduceAtHead()
        is Expression.Lam -> true
        is Expression.LetE -> true
        is Expression.Proj -> true
        is Expression.Const -> this.decl is Declaration.Def
        is Expression.Mdata -> this.expr.canReduceAtHead()
        is Expression.Bvar, is Expression.ForallE, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> false
    }
}

context(env: Environment)
private fun Expression.asNatLiteralValue(): NatValue? = when (this) {
    is Expression.NatVal -> this.natVal
    else -> if (this.isNatZeroCtorConst()) NatValue.ZERO else null
}

context(env: Environment)
private fun Expression.isNatLiteralPrimitiveConst(): Boolean = when (this) {
    is Expression.Const -> when (this.name.toStringDetailed()) {
        "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble" -> true
        else -> false
    }

    else -> false
}

context(env: Environment)
private fun Expression.isNatLiteralPrimitive(): Boolean = when (this) {
    is Expression.Const -> this.isNatLiteralPrimitiveConst()
    is Expression.App -> this.unfoldApp().first.isNatLiteralPrimitiveConst()
    else -> false
}

context(env: Environment)
private fun Expression.App.natLiteralPrimitiveArity(): Int? {
    val headConst = this.unfoldApp().first as? Expression.Const ?: return null
    return when (headConst.name.toStringDetailed()) {
        "Nat.succ" -> 1
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble" -> 2
        else -> null
    }
}


context(env: Environment)
private fun boolCtor(value: Boolean): Expression {
    val boolTypeIndex = env.findRootInductive("Bool")?.first
        ?: error("Nat literal reduction used without Bool inductive in environment")
    val ctorIndex = env.findChildNameIndex(boolTypeIndex, if (value) "true" else "false")
        ?: error("Nat literal reduction used without Bool.${if (value) "true" else "false"} constructor in environment")
    return env.addCustomExpr {
        Expression.Const(_name = ctorIndex, us = emptyList(), ie = it)
    }
}

context(env: Environment)
private fun Expression.App.tryReduceNatLiteral(levelSubst: Map<Int, Level>): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val headConst = headExpr as? Expression.Const ?: return null

    fun natArg(index: Int): NatValue? {
        val argExpr = args.getOrNull(index) ?: return null
        return argExpr.reduce(levelSubst).asNatLiteralValue()
    }

    return when (headConst.name.toStringDetailed()) {
        "Nat.succ" -> {
            val argNat = natArg(0) ?: return null
            env.addCustomExpr { Expression.NatVal(argNat + NatValue.ONE, it) }
        }

        "Nat.add" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            env.addCustomExpr { Expression.NatVal(lhs + rhs, it) }
        }

        "Nat.sub" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            env.addCustomExpr { Expression.NatVal(if (lhs >= rhs) lhs - rhs else NatValue.ZERO, it) }
        }

        "Nat.mul" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            env.addCustomExpr { Expression.NatVal(lhs * rhs, it) }
        }

        "Nat.pow" -> {
            val base = natArg(0) ?: return null
            val exponent = natArg(1)?.toIntOrNull() ?: return null
            env.addCustomExpr { Expression.NatVal(base.pow(exponent), it) }
        }

        "Nat.div" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            env.addCustomExpr { Expression.NatVal(lhs.divLean(rhs), it) }
        }

        "Nat.mod" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            env.addCustomExpr { Expression.NatVal(lhs.modLean(rhs), it) }
        }

        "Nat.beq" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            boolCtor(lhs == rhs)
        }

        "Nat.ble" -> {
            val lhs = natArg(0) ?: return null
            val rhs = natArg(1) ?: return null
            boolCtor(lhs <= rhs)
        }

        else -> null
    }
}

context(env: Environment)
private fun Expression.tryUnfoldReducibleHeadOnce(levelSubst: Map<Int, Level> = emptyMap()): Expression? {
    if (levelSubst.isNotEmpty()) {
        return this.instantiateLevelParams(levelSubst).tryUnfoldReducibleHeadOnce()
    }
    return when (this) {
        is Expression.Const -> {
            val defDecl = this.decl as? Declaration.Def ?: return null
            defDecl.valueExpr.instantiateLevelParams(this.composeLevelSubst(emptyMap()))
        }

        is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr))
        is Expression.Mdata -> this.expr
        is Expression.App -> {
            when (val fn = this.fnExpr) {
                is Expression.Lam -> fn.bodyExpr.applySubst(listOf(this.argExpr))
                is Expression.Const -> {
                    val defDecl = fn.decl as? Declaration.Def ?: return null
                    val fnUnfolded = defDecl.valueExpr.instantiateLevelParams(fn.composeLevelSubst(emptyMap()))
                    env.addCustomExpr { this.copy(fn = fnUnfolded.ie, ie = it) }
                }

                is Expression.Mdata -> env.addCustomExpr { this.copy(fn = fn.expr.ie, ie = it) }
                else -> null
            }
        }

        else -> null
    }
}

context(env: Environment)
private fun Expression.Proj.inferProjectionType(levelSubst: Map<Int, Level>, localCtx: List<Expression>): Expression {
    val structType0 = this.structExpr.inferType(levelSubst, localCtx)
    val structTypeExpr = structType0.whnf(localCtx = localCtx)
    val [structTypeHead, structTypeArgs] = structTypeExpr.unfoldApp()
    val structTypeConst = structTypeHead as? Expression.Const
        ?: error("Projection ${this.toStringDetailed()} expects structure type, got ${structTypeExpr.toStringDetailed()}")

    val inductiveDecl = this.typeDecl as? Inductive.InductiveVal
        ?: error("Projection ${this.toStringDetailed()} expects inductive type declaration for ${this.typeNameExpr}")

    check(structTypeConst.name == this.typeNameExpr) {
        "Projection ${this.toStringDetailed()} type name mismatch: expected ${this.typeNameExpr}, got ${structTypeConst.name}"
    }
    check(inductiveDecl.ctors.size == 1) {
        "Projection ${this.toStringDetailed()} requires exactly one constructor for ${this.typeNameExpr}"
    }
    check(inductiveDecl.numIndices == 0) {
        "Projection ${this.toStringDetailed()} is not allowed on indexed inductive ${this.typeNameExpr}"
    }
    check(structTypeArgs.size == inductiveDecl.numParams + inductiveDecl.numIndices) {
        "Projection ${this.toStringDetailed()} structure type has wrong arg count: expected ${inductiveDecl.numParams + inductiveDecl.numIndices}, got ${structTypeArgs.size}"
    }

    val constructorDecl = env.declarations[inductiveDecl.ctors.single()] as? Inductive.ConstructorVal
        ?: error("Projection ${this.toStringDetailed()} constructor declaration not found")

    check(this.projIndex in 0 until constructorDecl.numFields) {
        "Projection ${this.toStringDetailed()} index ${this.projIndex} out of range for ${this.typeNameExpr} with ${constructorDecl.numFields} fields"
    }
    check(constructorDecl.numParams == inductiveDecl.numParams) {
        "Projection ${this.toStringDetailed()} constructor/inductive parameter mismatch for ${this.typeNameExpr}"
    }

    val projectionLevelSubst = structTypeConst.composeLevelSubst(emptyMap())
    val paramArgs = structTypeArgs.take(constructorDecl.numParams)
    val structSort = structTypeExpr.inferSort(localCtx = localCtx)
    val isPropStructure = structSort.isLessOrEqual(Level.Zero)
    val nonPropFieldIndices = mutableSetOf<Int>()

    var ctorType: Expression = constructorDecl.typeExpr.instantiateLevelParams(projectionLevelSubst)
    repeat(constructorDecl.numParams + this.projIndex) { binderIndex ->
        val ctorForall = ctorType as? Expression.ForallE
            ?: error("Constructor ${constructorDecl.name} has too few binders while checking projection ${this.toStringDetailed()}")
        if (isPropStructure && binderIndex >= constructorDecl.numParams) {
            val priorFieldIndex = binderIndex - constructorDecl.numParams
            val priorFieldSort = ctorForall.typeExpr.inferSort(localCtx = localCtx)
            if (!priorFieldSort.isLessOrEqual(Level.Zero)) {
                nonPropFieldIndices += priorFieldIndex
            } else {
                check(!ctorForall.typeExpr.containsProjectionOf(this.typeNameExpr, nonPropFieldIndices)) {
                    "Projection ${this.toStringDetailed()} from proposition ${this.typeNameExpr} is not allowed because prior proposition field #$priorFieldIndex depends on prior non-proposition data"
                }
            }
        }
        val binderArg = if (binderIndex < constructorDecl.numParams) {
            paramArgs[binderIndex]
        } else {
            val priorFieldIndex = binderIndex - constructorDecl.numParams
            env.addCustomExpr {
                Expression.Proj(
                    typeName = this.typeNameIndex,
                    idx = priorFieldIndex,
                    struct = this@inferProjectionType.structExpr.ie,
                    ie = it,
                )
            }
        }
        ctorType = ctorForall.bodyExpr.applySubst(listOf(binderArg))
    }

    val targetFieldBinder = ctorType as? Expression.ForallE
        ?: error("Constructor ${constructorDecl.name} has too few fields for projection ${this.toStringDetailed()}")
    val projectedType = targetFieldBinder.typeExpr
    if (isPropStructure) {
        val projectedSort = projectedType.inferSort(localCtx = localCtx)
        check(projectedSort.isLessOrEqual(Level.Zero)) {
            "Projection ${this.toStringDetailed()} from proposition ${this.typeNameExpr} is not allowed because target field #${this.projIndex} is non-proposition ${projectedType.toStringDetailed()}"
        }
        check(!projectedType.containsProjectionOf(this.typeNameExpr, nonPropFieldIndices)) {
            "Projection ${this.toStringDetailed()} from proposition ${this.typeNameExpr} is not allowed because target field #${this.projIndex} depends on prior non-proposition data"
        }
    }

    return projectedType
}

context(env: Environment)
private fun Expression.containsProjectionOf(typeName: Name, projIndices: Set<Int>): Boolean {
    if (projIndices.isEmpty()) return false
    return when (this) {
        is Expression.App -> this.fnExpr.containsProjectionOf(typeName, projIndices)
                || this.argExpr.containsProjectionOf(typeName, projIndices)

        is Expression.ForallE -> this.typeExpr.containsProjectionOf(typeName, projIndices)
                || this.bodyExpr.containsProjectionOf(typeName, projIndices)

        is Expression.Lam -> this.typeExpr.containsProjectionOf(typeName, projIndices)
                || this.bodyExpr.containsProjectionOf(typeName, projIndices)

        is Expression.LetE -> this.typeExpr.containsProjectionOf(typeName, projIndices)
                || this.valueExpr.containsProjectionOf(typeName, projIndices)
                || this.bodyExpr.containsProjectionOf(typeName, projIndices)

        is Expression.Mdata -> this.expr.containsProjectionOf(typeName, projIndices)
        is Expression.Proj -> (this.typeNameExpr == typeName && this.projIndex in projIndices)
                || this.structExpr.containsProjectionOf(typeName, projIndices)

        else -> false
    }
}

context(env: Environment)
private fun Expression.App.tryReduceRecursor(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val recConst = headExpr as? Expression.Const ?: return null
    val recursorDecl = recConst.decl as? Inductive.RecursorVal ?: return null
    val recursorLevelSubst = recConst.composeLevelSubst(levelSubst)

    val majorArgIndex =
        recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors + recursorDecl.numIndices
    if (args.size <= majorArgIndex) return null

    val recursorArgsPrefixSize = recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors
    val prefixArgs = args.take(recursorArgsPrefixSize)

    fun applyRule(
        rule: Inductive.RecursorVal.RecursorRule,
        fieldArgs: List<Expression>,
    ): Expression {
        var reducedExpr: Expression = rule.rhsExpr.instantiateLevelParams(recursorLevelSubst)
        (prefixArgs + fieldArgs).map { it.instantiateLevelParams(levelSubst) }.forEach { substArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, substArg.ie, it) }
        }
        args.drop(majorArgIndex + 1).map { it.instantiateLevelParams(levelSubst) }.forEach { extraArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, extraArg.ie, it) }
        }
        return reducedExpr.reduce(localCtx = localCtx)
    }

    fun tryReduceCtorOrNatMajor(majorExpr: Expression): Expression? {
        val iotaMajorExpr = majorExpr.tryStringLitCtor() ?: majorExpr
        val [majorHead, majorArgs] = iotaMajorExpr.unfoldApp()

        val majorCtor = majorHead as? Expression.Const
        val constructorDecl = majorCtor?.decl as? Inductive.ConstructorVal
        if (majorCtor != null && constructorDecl != null) {
            val matchingRule = recursorDecl.rules.singleOrNull { rule ->
                rule.ctorName == majorCtor.name
            } ?: return null

            check(constructorDecl.numParams == recursorDecl.numParams) {
                "Recursor ${recursorDecl.name} and constructor ${constructorDecl.name} disagree on numParams"
            }
            check(constructorDecl.numFields == matchingRule.nfields) {
                "Recursor rule for ${constructorDecl.name} has wrong nfields: expected ${constructorDecl.numFields}, got ${matchingRule.nfields}"
            }

            if (majorArgs.size != constructorDecl.numParams + matchingRule.nfields) return null
            val fieldArgs = majorArgs.drop(constructorDecl.numParams)
            return applyRule(matchingRule, fieldArgs)
        }

        val majorNatLit = iotaMajorExpr as? Expression.NatVal
        if (majorNatLit != null) {
            val natRulesByFields: List<Pair<Int, Inductive.RecursorVal.RecursorRule>> =
                recursorDecl.rules.mapNotNull { rule ->
                    val ctorDecl = env.constructorByName[rule.ctorName] ?: return@mapNotNull null
                    val inductiveName = ctorDecl.inductName as? Name.Str ?: return@mapNotNull null
                    if (
                        inductiveName.pre == 0 &&
                        inductiveName.str == "Nat" &&
                        ctorDecl.numParams == recursorDecl.numParams &&
                        ctorDecl.numFields == rule.nfields
                    ) {
                        Pair(ctorDecl.numFields, rule)
                    } else {
                        null
                    }
                }
            if (natRulesByFields.size == recursorDecl.rules.size) {
                val zeroRule = natRulesByFields.singleOrNull { it.first == 0 }?.second
                val succRule = natRulesByFields.singleOrNull { it.first == 1 }?.second
                if (zeroRule != null && succRule != null) {
                    return if (majorNatLit.natVal.isZero()) {
                        applyRule(zeroRule, emptyList())
                    } else {
                        val predNat = env.addCustomExpr { Expression.NatVal(majorNatLit.natVal.minus(1L), it) }
                        applyRule(succRule, listOf(predNat))
                    }
                }
            }
        }

        return null
    }

    val majorWhnf = args[majorArgIndex].whnf(levelSubst, localCtx)
    tryReduceCtorOrNatMajor(majorWhnf)?.let { return it }

    val majorReduced = args[majorArgIndex].reduce(levelSubst, localCtx)
    tryReduceCtorOrNatMajor(majorReduced)?.let { return it }

    run {
        val inductiveDeclIndex = recursorDecl.all.singleOrNull() ?: return@run
        val inductiveDecl = env.declarations[inductiveDeclIndex] as? Inductive.InductiveVal ?: return@run
        if (inductiveDecl.isRec || inductiveDecl.numIndices != 0 || inductiveDecl.ctors.size != 1) return@run

        val singleRule = recursorDecl.rules.singleOrNull() ?: return@run
        val constructorDecl =
            env.declarations[inductiveDecl.ctors.single()] as? Inductive.ConstructorVal ?: return@run
        if (constructorDecl.numParams != recursorDecl.numParams) return@run
        if (constructorDecl.numFields != singleRule.nfields) return@run
        if (singleRule.ctorName != constructorDecl.name) return@run

        val fieldArgs = List(constructorDecl.numFields) { fieldIndex ->
            env.addCustomExpr {
                Expression.Proj(
                    typeName = inductiveDeclIndex,
                    idx = fieldIndex,
                    struct = majorReduced.ie,
                    ie = it
                )
            }
        }
        return applyRule(singleRule, fieldArgs)
    }

    if (!recursorDecl.k) return null
    val kRule = recursorDecl.rules.singleOrNull() ?: return null
    if (kRule.nfields != 0) return null
    val kCtorDecl = env.constructorByName[kRule.ctorName] ?: return null
    if (kCtorDecl.numFields != 0 || kCtorDecl.numParams != recursorDecl.numParams) return null
    val indexArgs = args.drop(recursorArgsPrefixSize).take(recursorDecl.numIndices)
    if (indexArgs.size != recursorDecl.numIndices) return null

    var ctorTail: Expression = kCtorDecl.typeExpr
    repeat(kCtorDecl.numParams + kCtorDecl.numFields) { binderIndex ->
        val ctorForall = ctorTail as? Expression.ForallE ?: return null
        val binderArg = if (binderIndex < kCtorDecl.numParams) args[binderIndex] else return null
        ctorTail = ctorForall.bodyExpr.applySubst(listOf(binderArg))
    }

    val [ctorResultHead, ctorResultArgs] = ctorTail.unfoldApp()
    val ctorResultConst = ctorResultHead as? Expression.Const ?: return null
    if (ctorResultConst.name != kCtorDecl.inductName) return null
    if (ctorResultArgs.size != recursorDecl.numParams + recursorDecl.numIndices) return null
    val expectedIndexArgs = ctorResultArgs.drop(recursorDecl.numParams)
    repeat(recursorDecl.numIndices) { index ->
        val expectedIndex = expectedIndexArgs[index].instantiateLevelParams(recursorLevelSubst)
        val actualIndex = indexArgs[index].instantiateLevelParams(recursorLevelSubst)
        if (!expectedIndex.isDefEq(actualIndex, localCtx, localCtx)) return null
    }

    return applyRule(kRule, emptyList())
}

context(env: Environment)
private fun Expression.App.tryReduceRecursorHead(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val recConst = headExpr as? Expression.Const ?: return null
    val recursorDecl = recConst.decl as? Inductive.RecursorVal ?: return null
    val recursorLevelSubst = recConst.composeLevelSubst(levelSubst)

    val majorArgIndex =
        recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors + recursorDecl.numIndices
    if (args.size <= majorArgIndex) return null

    val recursorArgsPrefixSize = recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors
    val prefixArgs = args.take(recursorArgsPrefixSize)

    fun applyRule(
        rule: Inductive.RecursorVal.RecursorRule,
        fieldArgs: List<Expression>,
    ): Expression {
        var reducedExpr: Expression = rule.rhsExpr.instantiateLevelParams(recursorLevelSubst)
        val appliedArgs = (prefixArgs + fieldArgs).map { it.instantiateLevelParams(levelSubst) }
        val extraArgs = args.drop(majorArgIndex + 1).map { it.instantiateLevelParams(levelSubst) }
        appliedArgs.forEach { substArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, substArg.ie, it) }
        }
        extraArgs.forEach { extraArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, extraArg.ie, it) }
        }
        return reducedExpr
    }

    val majorWhnf = args[majorArgIndex].whnf(levelSubst, localCtx)
    val iotaMajorWhnf = majorWhnf.tryStringLitCtor() ?: majorWhnf
    val [majorHead, majorArgs] = iotaMajorWhnf.unfoldApp()

    val majorCtor = majorHead as? Expression.Const
    val constructorDecl = majorCtor?.decl as? Inductive.ConstructorVal
    if (majorCtor != null && constructorDecl != null) {
        val matchingRule = recursorDecl.rules.singleOrNull { rule ->
            rule.ctorName == majorCtor.name
        } ?: return null

        check(constructorDecl.numParams == recursorDecl.numParams) {
            "Recursor ${recursorDecl.name} and constructor ${constructorDecl.name} disagree on numParams"
        }
        check(constructorDecl.numFields == matchingRule.nfields) {
            "Recursor rule for ${constructorDecl.name} has wrong nfields: expected ${constructorDecl.numFields}, got ${matchingRule.nfields}"
        }

        if (majorArgs.size != constructorDecl.numParams + matchingRule.nfields) return null
        val fieldArgs = majorArgs.drop(constructorDecl.numParams)
        return applyRule(matchingRule, fieldArgs)
    }

    val majorNatLit = iotaMajorWhnf as? Expression.NatVal
    if (majorNatLit != null) {
        val natRulesByFields: List<Pair<Int, Inductive.RecursorVal.RecursorRule>> =
            recursorDecl.rules.mapNotNull { rule ->
                val ctorDecl = env.constructorByName[rule.ctorName] ?: return@mapNotNull null
                val inductiveName = ctorDecl.inductName as? Name.Str ?: return@mapNotNull null
                if (
                    inductiveName.pre == 0 &&
                    inductiveName.str == "Nat" &&
                    ctorDecl.numParams == recursorDecl.numParams &&
                    ctorDecl.numFields == rule.nfields
                ) {
                    Pair(ctorDecl.numFields, rule)
                } else {
                    null
                }
            }
        if (natRulesByFields.size == recursorDecl.rules.size) {
            val zeroRule = natRulesByFields.singleOrNull { it.first == 0 }?.second
            val succRule = natRulesByFields.singleOrNull { it.first == 1 }?.second
            if (zeroRule != null && succRule != null) {
                return if (majorNatLit.natVal.isZero()) {
                    applyRule(zeroRule, emptyList())
                } else {
                    val predNat = env.addCustomExpr { Expression.NatVal(majorNatLit.natVal.minus(1L), it) }
                    applyRule(succRule, listOf(predNat))
                }
            }
        }
    }

    run {
        val inductiveDeclIndex = recursorDecl.all.singleOrNull() ?: return@run
        val inductiveDecl = env.declarations[inductiveDeclIndex] as? Inductive.InductiveVal ?: return@run
        if (inductiveDecl.isRec || inductiveDecl.numIndices != 0 || inductiveDecl.ctors.size != 1) return@run

        val singleRule = recursorDecl.rules.singleOrNull() ?: return@run
        val constructorDecl =
            env.declarations[inductiveDecl.ctors.single()] as? Inductive.ConstructorVal ?: return@run
        if (constructorDecl.numParams != recursorDecl.numParams) return@run
        if (constructorDecl.numFields != singleRule.nfields) return@run
        if (singleRule.ctorName != constructorDecl.name) return@run

        val fieldArgs = List(constructorDecl.numFields) { fieldIndex ->
            env.addCustomExpr {
                Expression.Proj(
                    typeName = inductiveDeclIndex,
                    idx = fieldIndex,
                    struct = majorWhnf.ie,
                    ie = it
                )
            }
        }
        return applyRule(singleRule, fieldArgs)
    }

    if (!recursorDecl.k) return null
    val kRule = recursorDecl.rules.singleOrNull() ?: return null
    if (kRule.nfields != 0) return null
    val kCtorDecl = env.constructorByName[kRule.ctorName] ?: return null
    if (kCtorDecl.numFields != 0 || kCtorDecl.numParams != recursorDecl.numParams) return null
    val indexArgs = args.drop(recursorArgsPrefixSize).take(recursorDecl.numIndices)
    if (indexArgs.size != recursorDecl.numIndices) return null

    var ctorTail: Expression = kCtorDecl.typeExpr
    repeat(kCtorDecl.numParams + kCtorDecl.numFields) { binderIndex ->
        val ctorForall = ctorTail as? Expression.ForallE ?: return null
        val binderArg = if (binderIndex < kCtorDecl.numParams) args[binderIndex] else return null
        ctorTail = ctorForall.bodyExpr.applySubst(listOf(binderArg))
    }

    val [ctorResultHead, ctorResultArgs] = ctorTail.unfoldApp()
    val ctorResultConst = ctorResultHead as? Expression.Const ?: return null
    if (ctorResultConst.name != kCtorDecl.inductName) return null
    if (ctorResultArgs.size != recursorDecl.numParams + recursorDecl.numIndices) return null
    val expectedIndexArgs = ctorResultArgs.drop(recursorDecl.numParams)
    repeat(recursorDecl.numIndices) { index ->
        val expectedIndex = expectedIndexArgs[index].instantiateLevelParams(recursorLevelSubst)
        val actualIndex = indexArgs[index].instantiateLevelParams(recursorLevelSubst)
        if (!expectedIndex.isDefEq(actualIndex, localCtx, localCtx)) {
            return null
        }
    }

    return applyRule(kRule, emptyList())
}

context(env: Environment)
private fun Expression.App.tryReduceQuot(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val quotConst = headExpr as? Expression.Const ?: return null
    val quotDecl = quotConst.decl as? Declaration.Quot ?: return null
    if (quotDecl.kind != Declaration.Quot.Kind.Lift && quotDecl.kind != Declaration.Quot.Kind.Ind) return null
    val arity = quotDecl.typeExpr.forallBinderCount()
    if (args.size < arity) return null

    val majorArg = args[arity - 1]
    val majorWhnf = majorArg.reduce(levelSubst, localCtx)
    val [majorHead, majorArgs] = majorWhnf.unfoldApp()
    val majorCtorConst = majorHead as? Expression.Const ?: return null
    val majorCtorDecl = majorCtorConst.decl as? Declaration.Quot ?: return null
    if (majorCtorDecl.kind != Declaration.Quot.Kind.Ctor) return null

    val ctorArity = majorCtorDecl.typeExpr.forallBinderCount()
    if (majorArgs.size < ctorArity || ctorArity == 0) return null
    val ctorValueArg = majorArgs[ctorArity - 1]

    val fnArg = when (quotDecl.kind) {
        Declaration.Quot.Kind.Lift -> args.getOrNull(arity - 3)?.instantiateLevelParams(levelSubst) ?: return null
        Declaration.Quot.Kind.Ind -> args.getOrNull(arity - 2)?.instantiateLevelParams(levelSubst) ?: return null
    }

    var reducedExpr: Expression = env.addCustomExpr {
        Expression.App(fn = fnArg.ie, arg = ctorValueArg.ie, ie = it)
    }
    args.drop(arity).map { it.instantiateLevelParams(levelSubst) }.forEach { extraArg: Expression ->
        reducedExpr = env.addCustomExpr { Expression.App(fn = reducedExpr.ie, arg = extraArg.ie, ie = it) }
    }
    return reducedExpr.reduce(localCtx = localCtx)
}

context(env: Environment)
private fun Expression.App.tryReduceQuotHead(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val quotConst = headExpr as? Expression.Const ?: return null
    val quotDecl = quotConst.decl as? Declaration.Quot ?: return null
    if (quotDecl.kind != Declaration.Quot.Kind.Lift && quotDecl.kind != Declaration.Quot.Kind.Ind) return null
    val arity = quotDecl.typeExpr.forallBinderCount()
    if (args.size < arity) return null

    val majorArg = args[arity - 1]
    val majorWhnf = majorArg.whnf(levelSubst, localCtx)
    val [majorHead, majorArgs] = majorWhnf.unfoldApp()
    val majorCtorConst = majorHead as? Expression.Const ?: return null
    val majorCtorDecl = majorCtorConst.decl as? Declaration.Quot ?: return null
    if (majorCtorDecl.kind != Declaration.Quot.Kind.Ctor) return null

    val ctorArity = majorCtorDecl.typeExpr.forallBinderCount()
    if (majorArgs.size < ctorArity || ctorArity == 0) return null
    val ctorValueArg = majorArgs[ctorArity - 1]

    val fnArg = when (quotDecl.kind) {
        Declaration.Quot.Kind.Lift -> args.getOrNull(arity - 3)?.instantiateLevelParams(levelSubst) ?: return null
        Declaration.Quot.Kind.Ind -> args.getOrNull(arity - 2)?.instantiateLevelParams(levelSubst) ?: return null
    }

    var reducedExpr: Expression = env.addCustomExpr {
        Expression.App(fn = fnArg.ie, arg = ctorValueArg.ie, ie = it)
    }
    args.drop(arity).map { it.instantiateLevelParams(levelSubst) }.forEach { extraArg: Expression ->
        reducedExpr = env.addCustomExpr { Expression.App(fn = reducedExpr.ie, arg = extraArg.ie, ie = it) }
    }
    return reducedExpr
}

context(env: Environment)
private fun Expression.forallBinderCount(): Int {
    var count = 0
    var tail: Expression = this
    while (tail is Expression.ForallE) {
        count += 1
        tail = tail.bodyExpr
    }
    return count
}

context(env: Environment)
private fun Expression.tryStructureEtaDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val leftKey = this.ie.toLong() and 0xffffffffL
    val rightKey = other.ie.toLong() and 0xffffffffL
    val guardKey = if (leftKey <= rightKey) {
        (leftKey shl 32) xor rightKey
    } else {
        (rightKey shl 32) xor leftKey
    }
    if (!env.structureEtaInProgress.add(guardKey)) return false
    try {
        if (!this.hasNoUnboundBvars(localCtxLeft.size) || !other.hasNoUnboundBvars(localCtxRight.size)) {
            return false
        }
        val leftType0 = this.inferType(localCtx = localCtxLeft)
        val rightType0 = other.inferType(localCtx = localCtxRight)
        val leftTypeExpr = leftType0.reduce(localCtx = localCtxLeft)
        val rightTypeExpr = rightType0.reduce(localCtx = localCtxRight)

        val [leftTypeHead, leftTypeArgs] = leftTypeExpr.unfoldApp()
        val [rightTypeHead, rightTypeArgs] = rightTypeExpr.unfoldApp()
        val leftTypeConst = leftTypeHead as? Expression.Const ?: return false
        val rightTypeConst = rightTypeHead as? Expression.Const ?: return false
        if (leftTypeConst.name != rightTypeConst.name) return false
        if (leftTypeArgs.size != rightTypeArgs.size) return false
        if (!leftTypeArgs.indices.all { leftTypeArgs[it].isDefEq(rightTypeArgs[it], localCtxLeft, localCtxRight) }) {
            return false
        }

        val typeNameIndex = env.nameIndices[leftTypeConst.name] ?: return false
        val structureDecl = env.declarations[typeNameIndex] as? Inductive.InductiveVal ?: return false
        if (structureDecl.isRec || structureDecl.ctors.size != 1 || structureDecl.numIndices != 0) {
            return false
        }
        val structureSort = leftTypeExpr.inferSort(localCtx = localCtxLeft)
        if (structureSort.isLessOrEqual(Level.Zero)) return false
        val constructorDecl =
            env.declarations[structureDecl.ctors.single()] as? Inductive.ConstructorVal ?: return false
        if (constructorDecl.numParams != structureDecl.numParams) return false
        fun Expression.constructorFieldArgsOrNull(): List<Expression>? {
            val [headExpr, args] = this.unfoldApp()
            val ctorConst = headExpr as? Expression.Const ?: return null
            val ctorHeadDecl = ctorConst.decl as? Inductive.ConstructorVal ?: return null
            if (ctorHeadDecl.name != constructorDecl.name) return null
            if (args.size != ctorHeadDecl.numParams + ctorHeadDecl.numFields) return null
            return args.drop(ctorHeadDecl.numParams)
        }

        val leftCtorFieldArgs = this.constructorFieldArgsOrNull()
        val rightCtorFieldArgs = other.constructorFieldArgsOrNull()
        val compareDirectCtorFields = leftCtorFieldArgs != null && rightCtorFieldArgs != null
        val leftProjectionLevelSubst = leftTypeConst.composeLevelSubst(emptyMap())
        val rightProjectionLevelSubst = rightTypeConst.composeLevelSubst(emptyMap())
        val leftParamArgs = leftTypeArgs.take(constructorDecl.numParams)
        val rightParamArgs = rightTypeArgs.take(constructorDecl.numParams)
        var leftCtorType: Expression = constructorDecl.typeExpr.instantiateLevelParams(leftProjectionLevelSubst)
        var rightCtorType: Expression = constructorDecl.typeExpr.instantiateLevelParams(rightProjectionLevelSubst)
        repeat(constructorDecl.numParams) { binderIndex ->
            val leftCtorForall = leftCtorType as? Expression.ForallE ?: return false
            val rightCtorForall = rightCtorType as? Expression.ForallE ?: return false
            leftCtorType = leftCtorForall.bodyExpr.applySubst(listOf(leftParamArgs[binderIndex]))
            rightCtorType = rightCtorForall.bodyExpr.applySubst(listOf(rightParamArgs[binderIndex]))
        }

        if (constructorDecl.numFields == 0) return true
        repeat(constructorDecl.numFields) { fieldIndex ->
            val leftFieldBinder = leftCtorType as? Expression.ForallE ?: return false
            val rightFieldBinder = rightCtorType as? Expression.ForallE ?: return false
            val leftFieldType = leftFieldBinder.typeExpr
            val rightFieldType = rightFieldBinder.typeExpr
            val lhsProj = env.addCustomExpr {
                Expression.Proj(
                    typeName = typeNameIndex,
                    idx = fieldIndex,
                    struct = this@tryStructureEtaDefEq.ie,
                    ie = it
                )
            }
            val rhsProj = env.addCustomExpr {
                Expression.Proj(typeName = typeNameIndex, idx = fieldIndex, struct = other.ie, ie = it)
            }
            val lhsFieldExpr = if (compareDirectCtorFields) leftCtorFieldArgs[fieldIndex] else lhsProj
            val rhsFieldExpr = if (compareDirectCtorFields) rightCtorFieldArgs[fieldIndex] else rhsProj
            val fieldEq = withDefEqCycleAssumptions {
                when {
                    leftFieldType.inferSort(localCtx = localCtxLeft).isLessOrEqual(Level.Zero) &&
                            rightFieldType.inferSort(localCtx = localCtxRight).isLessOrEqual(Level.Zero) -> true

                    else -> {
                        val leftFieldTypeWhnf = leftFieldType.reduce(localCtx = localCtxLeft)
                        val rightFieldTypeWhnf = rightFieldType.reduce(localCtx = localCtxRight)
                        val leftFieldFnType = leftFieldTypeWhnf as? Expression.ForallE
                        val rightFieldFnType = rightFieldTypeWhnf as? Expression.ForallE
                        if (leftFieldFnType != null && rightFieldFnType != null) {
                            lhsFieldExpr.tryCompareWithKnownFunctionType(
                                rhsFieldExpr,
                                leftFieldFnType.typeExpr,
                                rightFieldFnType.typeExpr,
                                localCtxLeft,
                                localCtxRight,
                            ) ?: lhsFieldExpr.isDefEq(rhsFieldExpr, localCtxLeft, localCtxRight)
                        } else {
                            lhsFieldExpr.isDefEq(rhsFieldExpr, localCtxLeft, localCtxRight)
                        }
                    }
                }
            }
            if (!fieldEq) return false
            leftCtorType = leftFieldBinder.bodyExpr.applySubst(listOf(lhsFieldExpr))
            rightCtorType = rightFieldBinder.bodyExpr.applySubst(listOf(rhsFieldExpr))
        }
        return true
    } finally {
        env.structureEtaInProgress.remove(guardKey)
    }
}

context(env: Environment)
private fun Expression.tryProofIrrelevanceDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    if (!this.hasNoUnboundBvars(localCtxLeft.size) || !other.hasNoUnboundBvars(localCtxRight.size)) {
        return false
    }
    val thisTy = this.inferType(localCtx = localCtxLeft)
    val otherTy = other.inferType(localCtx = localCtxRight)
    val thisSort = thisTy.inferSort(localCtx = localCtxLeft)
    val otherSort = otherTy.inferSort(localCtx = localCtxRight)
    if (!thisSort.isLessOrEqual(Level.Zero) || !otherSort.isLessOrEqual(Level.Zero)) {
        return false
    }
    return thisTy.isDefEq(otherTy, localCtxLeft, localCtxRight)
}

context(env: Environment)
fun Expression.inferSort(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
): Level {
    val tyWhnf = this.inferType(levelSubst, localCtx)
    val whnfTyExpr = tyWhnf.whnf(localCtx = localCtx)
    val sort = whnfTyExpr as? Expression.Sort
        ?: error("Expected Sort type for ${this.toStringDetailed()}, got ${whnfTyExpr.toStringDetailed()}")
    return sort.level
}

context(env: Environment)
private fun Expression.tryEtaReduce(): Expression? {
    fun Expression.Lam.tryEtaReduceHead(): Expression? {
        // Reduce body/arg first so `fun x => f x` shape can emerge after reduction.
        val reducedBody = this.bodyExpr.reduce()
        var bodyExprToCheck: Expression = if (reducedBody != this.bodyExpr) reducedBody else this.bodyExpr
        while (true) {
            val bodyApp = bodyExprToCheck as? Expression.App ?: return null
            val bodyArg = bodyApp.argExpr as? Expression.Bvar
            if (bodyArg != null) {
                if (bodyArg.bvar != 0) return null
                val fnExpr = bodyApp.fnExpr
                if (fnExpr.containsLooseBvarZero()) return null
                return fnExpr.dropOuterBinder()
            }
            val reducedArg = bodyApp.argExpr.reduce()
            if (reducedArg == bodyApp.argExpr) return null
            bodyExprToCheck = env.addCustomExpr {
                Expression.App(fn = bodyApp.fnExpr.ie, arg = reducedArg.ie, ie = it)
            }
        }
    }

    val lam = this as? Expression.Lam ?: return null
    val reducedBody = lam.bodyExpr.reduce()
    val lamToCheck = if (reducedBody == lam.bodyExpr) {
        lam
    } else {
        env.addCustomExpr { lam.copy(body = reducedBody.ie, ie = it) } as? Expression.Lam ?: return null
    }
    lamToCheck.tryEtaReduceHead()?.let { return it }

    val innerLam = lamToCheck.bodyExpr as? Expression.Lam ?: return null
    val reducedInner = innerLam.tryEtaReduce() ?: return null
    val rebuiltLam = env.addCustomExpr { lamToCheck.copy(body = reducedInner.ie, ie = it) } as? Expression.Lam
        ?: return null

    return rebuiltLam.tryEtaReduceHead() ?: rebuiltLam
}

context(env: Environment)
private fun Expression.containsLooseBvarZero(depth: Int = 0): Boolean {
    return when (this) {
        is Expression.Bvar -> this.bvar == depth
        is Expression.App -> this.fnExpr.containsLooseBvarZero(depth) || this.argExpr.containsLooseBvarZero(depth)
        is Expression.ForallE -> this.typeExpr.containsLooseBvarZero(depth) || this.bodyExpr.containsLooseBvarZero(depth + 1)
        is Expression.Lam -> this.typeExpr.containsLooseBvarZero(depth) || this.bodyExpr.containsLooseBvarZero(depth + 1)
        is Expression.LetE ->
            this.typeExpr.containsLooseBvarZero(depth) ||
                    this.valueExpr.containsLooseBvarZero(depth) ||
                    this.bodyExpr.containsLooseBvarZero(depth + 1)

        is Expression.Mdata -> this.expr.containsLooseBvarZero(depth)
        is Expression.Proj -> this.structExpr.containsLooseBvarZero(depth)
        is Expression.Const, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> false
    }
}

context(env: Environment)
private fun Expression.maxLooseBVarIndex(): Int {
    env.maxLooseBVarIndexCache[this.ie]?.let { return it }

    fun Int.descendBinder(): Int = if (this < 0) -1 else this - 1

    val result = when (this) {
        is Expression.Bvar -> this.bvar
        is Expression.App -> maxOf(this.fnExpr.maxLooseBVarIndex(), this.argExpr.maxLooseBVarIndex())
        is Expression.ForallE -> maxOf(
            this.typeExpr.maxLooseBVarIndex(),
            this.bodyExpr.maxLooseBVarIndex().descendBinder()
        )

        is Expression.Lam -> maxOf(this.typeExpr.maxLooseBVarIndex(), this.bodyExpr.maxLooseBVarIndex().descendBinder())
        is Expression.LetE -> maxOf(
            this.typeExpr.maxLooseBVarIndex(),
            this.valueExpr.maxLooseBVarIndex(),
            this.bodyExpr.maxLooseBVarIndex().descendBinder(),
        )

        is Expression.Mdata -> this.expr.maxLooseBVarIndex()
        is Expression.Proj -> this.structExpr.maxLooseBVarIndex()
        is Expression.Const, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> -1
    }

    env.maxLooseBVarIndexCache[this.ie] = result
    return result
}

context(env: Environment)
private fun Expression.hasNoUnboundBvars(localCtxSize: Int, depth: Int = 0): Boolean {
    if (this.maxLooseBVarIndex() < depth + localCtxSize) return true
    return when (this) {
        is Expression.Bvar -> this.bvar < depth + localCtxSize
        is Expression.App -> this.fnExpr.hasNoUnboundBvars(localCtxSize, depth) &&
                this.argExpr.hasNoUnboundBvars(localCtxSize, depth)

        is Expression.ForallE -> this.typeExpr.hasNoUnboundBvars(localCtxSize, depth) &&
                this.bodyExpr.hasNoUnboundBvars(localCtxSize, depth + 1)

        is Expression.Lam -> this.typeExpr.hasNoUnboundBvars(localCtxSize, depth) &&
                this.bodyExpr.hasNoUnboundBvars(localCtxSize, depth + 1)

        is Expression.LetE ->
            this.typeExpr.hasNoUnboundBvars(localCtxSize, depth) &&
                    this.valueExpr.hasNoUnboundBvars(localCtxSize, depth) &&
                    this.bodyExpr.hasNoUnboundBvars(localCtxSize, depth + 1)

        is Expression.Mdata -> this.expr.hasNoUnboundBvars(localCtxSize, depth)
        is Expression.Proj -> this.structExpr.hasNoUnboundBvars(localCtxSize, depth)
        is Expression.Const, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> true
    }
}

context(env: Environment)
private fun Expression.dropOuterBinder(): Expression {
    return this.rewriteBinders { bvarExpr, depth ->
        when {
            bvarExpr.bvar < depth -> bvarExpr
            bvarExpr.bvar == depth -> error("Cannot drop binder: expression still references removed binder in ${this@dropOuterBinder.toStringDetailed()}")
            else -> env.addCustomExpr {
                bvarExpr.copy(bvar = bvarExpr.bvar - 1, ie = it)
            }
        }
    }
}

context(env: Environment)
fun Expression.dropOuterBinders(count: Int): Expression {
    var result = this
    repeat(count) {
        result = result.dropOuterBinder()
    }
    return result
}

context(env: Environment)
fun Expression.lift(amount: Int): Expression {
    if (amount == 0) return this
    val cacheKey = (amount.toLong() shl 32) xor (this.ie.toLong() and 0xffffffffL)
    env.liftCache[cacheKey]?.let { return it }

    val result = this.rewriteBinders { bvarExpr, depth -> // MEM: 3 GB
        if (bvarExpr.bvar >= depth) {
            env.addCustomExpr { // MEM: 750 MB
                bvarExpr.copy(bvar = bvarExpr.bvar + amount, ie = it) // MEM: 150 MB
            }
        } else {
            bvarExpr
        }
    }
    env.liftCache[cacheKey] = result
    return result
}

context(env: Environment)
fun Expression.instantiateLevelParams(subst: Map<Int, Level>): Expression {
    if (subst.isEmpty()) return this
    return when (this) {
        is Expression.Bvar -> this
        is Expression.NatVal -> this
        is Expression.StrVal -> this

        is Expression.Sort -> {
            val newLevel = this.level.instantiateLevelParams(subst)
            if (newLevel == this.level) this else env.addCustomExpr { this.copy(sort = newLevel.il, ie = it) }
        }

        is Expression.Const -> {
            val newUs = this.levels.map { it.instantiateLevelParams(subst).il }
            val oldUs = this.levels.map { it.il }
            if (newUs == oldUs) this else env.addCustomExpr { this.copy(us = newUs, ie = it) }
        }

        is Expression.App -> {
            val newFn = this.fnExpr.instantiateLevelParams(subst)
            val newArg = this.argExpr.instantiateLevelParams(subst)
            if (newFn == this.fnExpr && newArg == this.argExpr) {
                this
            } else {
                env.addCustomExpr { this.copy(fn = newFn.ie, arg = newArg.ie, ie = it) }
            }
        }

        is Expression.ForallE -> {
            val newType = this.typeExpr.instantiateLevelParams(subst)
            val newBody = this.bodyExpr.instantiateLevelParams(subst)
            if (newType == this.typeExpr && newBody == this.bodyExpr) {
                this
            } else {
                env.addCustomExpr { this.copy(type = newType.ie, body = newBody.ie, ie = it) }
            }
        }

        is Expression.Lam -> {
            val newType = this.typeExpr.instantiateLevelParams(subst)
            val newBody = this.bodyExpr.instantiateLevelParams(subst)
            if (newType == this.typeExpr && newBody == this.bodyExpr) {
                this
            } else {
                env.addCustomExpr { this.copy(type = newType.ie, body = newBody.ie, ie = it) }
            }
        }

        is Expression.LetE -> {
            val newType = this.typeExpr.instantiateLevelParams(subst)
            val newValue = this.valueExpr.instantiateLevelParams(subst)
            val newBody = this.bodyExpr.instantiateLevelParams(subst)
            if (newType == this.typeExpr && newValue == this.valueExpr && newBody == this.bodyExpr) {
                this
            } else {
                env.addCustomExpr { this.copy(type = newType.ie, value = newValue.ie, body = newBody.ie, ie = it) }
            }
        }

        is Expression.Mdata -> {
            val newExpr = this.expr.instantiateLevelParams(subst)
            if (newExpr == this.expr) this else env.addCustomExpr { this.copy(_expr = newExpr.ie, ie = it) }
        }

        is Expression.Proj -> {
            val newStruct = this.structExpr.instantiateLevelParams(subst)
            if (newStruct == this.structExpr) this else env.addCustomExpr { this.copy(struct = newStruct.ie, ie = it) }
        }
    }
}

context(env: Environment)
fun Expression.applySubst(subst: List<Expression>): Expression {
    if (subst.isEmpty()) return this
    val singleSubstKey: Long? = if (subst.size == 1) {
        (this.ie.toLong() shl 32) xor (subst[0].ie.toLong() and 0xffffffffL)
    } else {
        null
    }
    if (singleSubstKey != null) {
        env.applySubstSingleCache[singleSubstKey]?.let { return it }
    }

    val liftedSubstCache = mutableMapOf<Long, Expression>()
    fun getLiftedSubst(index: Int, depth: Int): Expression {
        val cacheKey = (depth.toLong() shl 32) xor (index.toLong() and 0xffffffffL)
        return liftedSubstCache.getOrPut(cacheKey) {
            subst[index].lift(depth)
        }
    }

    val result = this.rewriteBinders { bvarExpr, currentDepth -> // MEM: 11 GB
        when {
            bvarExpr.bvar < currentDepth -> bvarExpr
            bvarExpr.bvar - currentDepth < subst.size ->
                getLiftedSubst(bvarExpr.bvar - currentDepth, currentDepth) // MEM: 3 GB

            else -> {
                env.addCustomExpr { // MEM: 2 GB
                    bvarExpr.copy(bvar = bvarExpr.bvar - subst.size, ie = it) // MEM: 490 MB
                }
            }
        }
    }
    if (singleSubstKey != null) {
        env.applySubstSingleCache[singleSubstKey] = result
    }
    return result
}

context(env: Environment)
private fun Expression.rewriteBinders(
    depth: Int = 0,
    rewriteBvar: (Expression.Bvar, Int) -> Expression
): Expression { // MEM: 11 GB
    val cache = mutableMapOf<Long, Expression>()

    fun Expression.rewriteAt(currentDepth: Int): Expression {
        val cacheKey = (currentDepth.toLong() shl 32) xor (this.ie.toLong() and 0xffffffffL)
        cache[cacheKey]?.let { return it }
        if (this.maxLooseBVarIndex() < currentDepth) {
            cache[cacheKey] = this
            return this
        }

        val result = when (this) {
            is Expression.Bvar -> rewriteBvar(this, currentDepth)

            is Expression.App -> {
                val newFn = this.fnExpr.rewriteAt(currentDepth) // MEM: 9.7 GB
                val newArg = this.argExpr.rewriteAt(currentDepth) // MEM: 9.5 GB
                if (newFn === this.fnExpr && newArg === this.argExpr) {
                    this
                } else {
                    env.addCustomExpr { // MEM: 5.4 GB
                        this.copy(fn = newFn.ie, arg = newArg.ie, ie = it) // MEM: 1.3 GB
                    }
                }
            }

            is Expression.ForallE -> {
                val newType = this.typeExpr.rewriteAt(currentDepth) // MEM: 1.3 GB
                val newBody = this.bodyExpr.rewriteAt(currentDepth + 1) // MEM: 2 GB
                if (newType === this.typeExpr && newBody === this.bodyExpr) {
                    this
                } else {
                    env.addCustomExpr {// MEM: 120 MB
                        this.copy(type = newType.ie, body = newBody.ie, ie = it)
                    }
                }
            }

            is Expression.Lam -> {
                val newType = this.typeExpr.rewriteAt(currentDepth) // MEM: 5.9 GB
                val newBody = this.bodyExpr.rewriteAt(currentDepth + 1) // MEM: 9.6 GB
                if (newType === this.typeExpr && newBody === this.bodyExpr) {
                    this
                } else {
                    env.addCustomExpr { // MEM: 800 MB
                        this.copy(type = newType.ie, body = newBody.ie, ie = it) // MEM: 180 MB
                    }
                }
            }

            is Expression.LetE -> {
                val newType = this.typeExpr.rewriteAt(currentDepth) // MEM: 110 MB
                val newValue = this.valueExpr.rewriteAt(currentDepth)
                val newBody = this.bodyExpr.rewriteAt(currentDepth + 1)
                if (newType === this.typeExpr && newValue === this.valueExpr && newBody === this.bodyExpr) {
                    this
                } else {
                    env.addCustomExpr {
                        this.copy(type = newType.ie, value = newValue.ie, body = newBody.ie, ie = it)
                    }
                }
            }

            is Expression.Mdata -> {
                val newExpr = this.expr.rewriteAt(currentDepth)
                if (newExpr === this.expr) {
                    this
                } else {
                    env.addCustomExpr {
                        this.copy(_expr = newExpr.ie, ie = it)
                    }
                }
            }

            is Expression.Proj -> {
                val newStruct = this.structExpr.rewriteAt(currentDepth) // MEM: 190 MB
                if (newStruct === this.structExpr) {
                    this
                } else {
                    env.addCustomExpr {
                        this.copy(struct = newStruct.ie, ie = it)
                    }
                }
            }

            else -> this
        }

        cache[cacheKey] = result
        return result
    }

    return this.rewriteAt(depth)
}

context(env: Environment)
fun Level.instantiateLevelParams(subst: Map<Int, Level>): Level {
    if (env.shouldLog2) println(this.toStringDetailed())
    return when (this) {
        Level.Zero -> this
        is Level.Param -> subst[this.il] ?: this

        is Level.Succ -> {
            val newLevel = this.level.instantiateLevelParams(subst)
            if (newLevel == this.level) {
                this
            } else {
                env.addCustomSuccLevel(newLevel.il)
            }
        }

        is Level.Max -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                env.addCustomMaxLevel(newLeft.il, newRight.il)
            }
        }

        is Level.Imax -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                env.addCustomImaxLevel(newLeft.il, newRight.il)
            }
        }
    }
}

// TODO: second item in pair is currently never used
private fun Environment.findRootInductive(shortName: String): Pair<Int, Inductive.InductiveVal>? {
    return this.rootInductiveByShortName[shortName]
}

private fun Environment.findChildNameIndex(parentNameIndex: Int, shortName: String): Int? {
    return this.names.toList()
        .firstOrNull { entry ->
            val nameIndex = entry.first
            val name = entry.second
            nameIndex != 0 &&
                    name is Name.Str &&
                    name.pre == parentNameIndex &&
                    name.str == shortName
        }
        ?.first
}

context(env: Environment)
private fun Expression.Const.composeLevelSubst(outer: Map<Int, Level>): Map<Int, Level> {
    fun Expression.Const.levelSubstMap(): Map<Int, Level> {
        val params = this.decl.levelParams
        check(params.size == this.levels.size) {
            "Universe argument mismatch for ${this.toStringDetailed()}: expected ${params.size}, got ${this.levels.size}"
        }
        return params.indices.associate { index ->
            params[index].il to this.levels[index]
        }
    }

    val inner = this.levelSubstMap()
    if (inner.isEmpty()) return emptyMap()
    if (outer.isEmpty()) return inner
    return inner.mapValues { entry -> entry.value.instantiateLevelParams(outer) }
}
