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
    var valueExpr = this
    var expectedExpr = expectedType
    var ctx = localCtx
    while (true) {
        val expectedTypeWhnf = expectedExpr.whnf(localCtx = ctx)
        val valueLam = valueExpr as? Expression.Lam
        val expectedForall = expectedTypeWhnf as? Expression.ForallE
        if (valueLam != null && expectedForall != null) {
            val _ = valueLam.typeExpr.inferSort(localCtx = ctx)
            if (!valueLam.typeExpr.isDefEq(expectedForall.typeExpr, ctx, ctx)) {
                return false
            }
            valueExpr = valueLam.bodyExpr
            expectedExpr = expectedForall.bodyExpr
            ctx = env.consLocalCtx(valueLam.typeExpr, ctx)
            continue
        }
        break
    }

    val inferredValueType = valueExpr.inferType(localCtx = ctx)
    if (env.shouldLog) println("inferred type of value: ${inferredValueType/*.toStringDetailed()*/}")
    if (env.shouldLog) {
        println("expected type detailed: ${expectedExpr.toStringDetailed()}")
        println("inferred type detailed: ${inferredValueType.toStringDetailed()}")
    }
    return expectedExpr.isDefEq(inferredValueType, ctx, ctx)
}

context(env: Environment)
fun Expression.isDefEq(
    other: Expression,
    localCtxLeft: List<Expression> = emptyList(),
    localCtxRight: List<Expression> = emptyList(),
): Boolean {
    env.defEqCalls += 1
    val leftCtxId = env.localCtxId(localCtxLeft)
    val rightCtxId = env.localCtxId(localCtxRight)
    val cacheKey = if (
        this.ie < other.ie ||
        (this.ie == other.ie && leftCtxId <= rightCtxId)
    ) {
        DefEqCacheKey(this.ie, other.ie, leftCtxId, rightCtxId)
    } else {
        DefEqCacheKey(other.ie, this.ie, rightCtxId, leftCtxId)
    }
    env.defEqCache[cacheKey]?.let { cached ->
        env.defEqCacheHits += 1
        return cached
    }
    if (!env.defEqInProgress.add(cacheKey)) {
        env.defEqInProgressSkips += 1
        return false
    }
    val inProgressSkipsBefore = env.defEqInProgressSkips
    val result = try {
        when {
            this === other || this.sameShape(other) -> true
            this.tryNatLiteralDefEq(other, localCtxLeft, localCtxRight) -> true
            this.tryNatOffsetDefEq(other, localCtxLeft, localCtxRight) == true -> true
            this.tryProofIrrelevanceDefEqNoLog(other, localCtxLeft, localCtxRight) -> true
            else -> {
                val leftProjectionDelta = this.tryProjectionDeltaStep()
                val rightProjectionDelta = other.tryProjectionDeltaStep()
                if (leftProjectionDelta != null || rightProjectionDelta != null) {
                    when {
                        leftProjectionDelta != null && rightProjectionDelta != null ->
                            leftProjectionDelta.isDefEq(rightProjectionDelta, localCtxLeft, localCtxRight)

                        leftProjectionDelta != null ->
                            leftProjectionDelta.isDefEq(other, localCtxLeft, localCtxRight)

                        else -> this.isDefEq(rightProjectionDelta!!, localCtxLeft, localCtxRight)
                    }
                } else {
                    this.tryProjectionLikeCongruence(other, localCtxLeft, localCtxRight)
                        ?: this.tryLazyDeltaDefEq(other, localCtxLeft, localCtxRight)
                        ?: run {
                            val leftWhnf = if (this.isWhnfByShape()) this else this.whnf(localCtx = localCtxLeft)
                            val rightWhnf = if (other.isWhnfByShape()) other else other.whnf(localCtx = localCtxRight)
                            leftWhnf === rightWhnf ||
                                    leftWhnf.isDefEqWhnf(rightWhnf, localCtxLeft, localCtxRight) ||
                                    leftWhnf.tryProofIrrelevanceDefEqNoLog(
                                        rightWhnf,
                                        localCtxLeft,
                                        localCtxRight,
                                    )
                        }
                }
            }
        }
    } finally {
        env.defEqInProgress.remove(cacheKey)
    }
    if (result || env.defEqInProgressSkips == inProgressSkipsBefore) {
        env.defEqCache[cacheKey] = result
    }
    return result
}

context(env: Environment)
private fun Expression.trySyntacticEtaContract(): Expression? {
    val lambda = this as? Expression.Lam ?: return null
    val body = lambda.bodyExpr as? Expression.App ?: return null
    val argument = body.argExpr as? Expression.Bvar ?: return null
    if (argument.bvar != 0 || body.fnExpr.containsLooseBvarZero()) return null
    return body.fnExpr.dropOuterBinder()
}

context(env: Environment)
private fun Expression.unfoldDefinitionOnce(): Expression? {
    val spine = this.asAppSpine()
    val constant = spine.first as? Expression.Const ?: return null
    val declaration = constant.decl as? Declaration.Def ?: return null
    return declaration.valueExpr
        .instantiateLevelParams(constant.composeLevelSubst(emptyMap()))
        .applyArgs(spine.second)
}

context(env: Environment)
private fun Expression.tryNatOffsetDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    if (this.asNatLiteralValue()?.isZero() == true && other.asNatLiteralValue()?.isZero() == true) return true
    val leftPred = this.natPredecessorOrNull() ?: return null
    val rightPred = other.natPredecessorOrNull() ?: return null
    return leftPred.isDefEq(rightPred, localCtxLeft, localCtxRight)
}

context(env: Environment)
private fun Expression.natPredecessorOrNull(): Expression? {
    if (this is Expression.NatVal && !this.natVal.isZero()) {
        return env.addCustomExpr { Expression.NatVal(this.natVal.minus(1L), it) }
    }
    val app = this as? Expression.App ?: return null
    val spine = app.unfoldApp()
    val constant = spine.first as? Expression.Const ?: return null
    if (constant.name.toStringDetailed() != "Nat.succ") return null
    return spine.second.singleOrNull()
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

private data class ProjectionAppShape(
    val inductiveNameIndex: Int,
    val fieldIndex: Int,
    val structExpr: Expression,
    val extraArgs: List<Expression>,
)

private data class NatLiteralRecursorRules(
    val zeroRule: Inductive.RecursorVal.RecursorRule,
    val succRule: Inductive.RecursorVal.RecursorRule,
)

context(env: Environment)
private fun Inductive.RecursorVal.natLiteralRecursorRules(): NatLiteralRecursorRules? {
    val natRulesByFields = this.rules.mapNotNull { rule ->
        val ctorDecl = env.constructorByName[rule.ctorName] ?: return@mapNotNull null
        val inductiveName = ctorDecl.inductName as? Name.Str ?: return@mapNotNull null
        if (
            inductiveName.pre == 0 &&
            inductiveName.str == "Nat" &&
            ctorDecl.numParams == this.numParams &&
            ctorDecl.numFields == rule.nfields
        ) {
            Pair(ctorDecl.numFields, rule)
        } else {
            null
        }
    }
    if (natRulesByFields.size != this.rules.size) return null
    val zeroRule = natRulesByFields.singleOrNull { it.first == 0 }?.second ?: return null
    val succRule = natRulesByFields.singleOrNull { it.first == 1 }?.second ?: return null
    return NatLiteralRecursorRules(zeroRule, succRule)
}

context(env: Environment)
private fun tryReduceNatValueRecursorMajor(
    recursorDecl: Inductive.RecursorVal,
    majorExpr: Expression,
    applyRule: (Inductive.RecursorVal.RecursorRule, List<Expression>) -> Expression,
): Expression? {
    val majorNatLit = majorExpr as? Expression.NatVal ?: return null
    val natRules = recursorDecl.natLiteralRecursorRules() ?: return null
    return if (majorNatLit.natVal.isZero()) {
        applyRule(natRules.zeroRule, emptyList())
    } else {
        val predNat = env.addCustomExpr { Expression.NatVal(majorNatLit.natVal.minus(1L), it) }
        applyRule(natRules.succRule, listOf(predNat))
    }
}

context(env: Environment)
private fun Expression.tryLazyDeltaDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    var left = this
    var right = other
    var changed = false
    while (true) {
        if (
            left === right ||
            left.sameShape(right) ||
            left.tryNatLiteralDefEq(right, localCtxLeft, localCtxRight) ||
            left.tryNatOffsetDefEq(right, localCtxLeft, localCtxRight) == true ||
            left.tryProofIrrelevanceDefEqNoLog(right, localCtxLeft, localCtxRight)
        ) {
            return true
        }

        val contractedLeft = left.trySyntacticEtaContract()
        if (contractedLeft != null) {
            left = contractedLeft
            changed = true
            continue
        }
        val contractedRight = right.trySyntacticEtaContract()
        if (contractedRight != null) {
            right = contractedRight
            changed = true
            continue
        }

        left.trySameHeadConstCongruence(right, localCtxLeft, localCtxRight)?.let { return it }

        val leftStep = left.tryLazyDeltaStep(localCtxLeft)
        val rightStep = right.tryLazyDeltaStep(localCtxRight)
        if (leftStep == null && rightStep == null) {
            left.trySameHeadConstCongruence(right, localCtxLeft, localCtxRight)?.let { return it }
            return if (changed) left.isDefEq(right, localCtxLeft, localCtxRight) else null
        }

        val choice = chooseLazyDeltaSide(leftStep, rightStep)
        when (choice) {
            LazyDeltaChoice.Left -> left = leftStep!!.unfoldedExpr
            LazyDeltaChoice.Right -> right = rightStep!!.unfoldedExpr
            LazyDeltaChoice.Both -> {
                left = leftStep!!.unfoldedExpr
                right = rightStep!!.unfoldedExpr
            }

            null -> return null
        }
        changed = true
    }
}

context(env: Environment)
private fun Expression.trySameHeadConstCongruence(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
    fallbackToRawArgs: Boolean = true,
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
    val leftProjectionInfo = leftConst.projectionReductionInfo()
    val rightProjectionInfo = rightConst.projectionReductionInfo()
    if (
        leftProjectionInfo != null &&
        rightProjectionInfo != null &&
        leftArgs.size >= leftProjectionInfo.arity &&
        rightArgs.size >= rightProjectionInfo.arity
    ) {
        return null
    }
    val levelsMatch = leftConst.levels == rightConst.levels ||
            leftConst.levels.zip(rightConst.levels).all { levelPair ->
                levelPair.first.isEqual(levelPair.second)
            }
    if (!levelsMatch) return null
    if (env.shouldLog) {
        println("i: sameHeadConstCongruence head=${leftConst.name.toStringDetailed()} argCount=${leftArgs.size} time=${env.clock.elapsedNow()}")
    }
    if (!fallbackToRawArgs) return null
    for (index in leftArgs.indices) {
        val argumentMatches = leftArgs[index].isDefEq(rightArgs[index], localCtxLeft, localCtxRight)
        if (!argumentMatches) {
            if (env.shouldLog) {
                println("sameHeadConstCongruence arg mismatch at index=$index")
                println("left arg: ${leftArgs[index].toStringDetailed()}")
                println("right arg: ${rightArgs[index].toStringDetailed()}")
                println("left nat literal: ${leftArgs[index].tryRecognizeNatLiteral(emptyMap(), localCtxLeft)}")
                println("right nat literal: ${rightArgs[index].tryRecognizeNatLiteral(emptyMap(), localCtxRight)}")
            }
            return null
        }
    }
    return true
}

context(env: Environment)
private fun Expression.tryProjectionDeltaStep(): Expression? = when (this) {
    is Expression.App -> this.tryReduceProjectionApp()
    else -> null
}

context(env: Environment)
private fun Expression.projectionAppShapeOrNull(): ProjectionAppShape? {
    return when (this) {
        is Expression.Proj -> ProjectionAppShape(
            inductiveNameIndex = this.typeNameIndex,
            fieldIndex = this.projIndex,
            structExpr = this.structExpr,
            extraArgs = emptyList(),
        )

        is Expression.App -> {
            val spine = this.asAppSpine()
            val headExpr = spine.first
            val args = spine.second
            when (headExpr) {
                is Expression.Proj -> ProjectionAppShape(
                    inductiveNameIndex = headExpr.typeNameIndex,
                    fieldIndex = headExpr.projIndex,
                    structExpr = headExpr.structExpr,
                    extraArgs = args,
                )

                else -> null
            }
        }

        else -> null
    }
}

context(env: Environment)
private fun Expression.tryProjectionLikeCongruence(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftProjection = this.projectionAppShapeOrNull() ?: return null
    val rightProjection = other.projectionAppShapeOrNull() ?: return null
    if (leftProjection.inductiveNameIndex != rightProjection.inductiveNameIndex) return null
    if (leftProjection.fieldIndex != rightProjection.fieldIndex) return null
    if (leftProjection.extraArgs.size != rightProjection.extraArgs.size) return null
    if (env.shouldLog) {
        println(
            "i: projectionCongruence left=${this.ie} right=${other.ie} " +
                    "field=${leftProjection.inductiveNameIndex}.${leftProjection.fieldIndex} " +
                    "structs=${leftProjection.structExpr.ie}:${rightProjection.structExpr.ie} " +
                    "extraArgs=${leftProjection.extraArgs.size} time=${env.clock.elapsedNow()}"
        )
    }
    if (!leftProjection.structExpr.isDefEq(rightProjection.structExpr, localCtxLeft, localCtxRight)) {
        return null
    }
    for (index in leftProjection.extraArgs.lastIndex downTo 0) {
        if (!leftProjection.extraArgs[index].isDefEq(rightProjection.extraArgs[index], localCtxLeft, localCtxRight)) {
            return null
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
    for (index in leftArgs.indices) {
        val argumentMatches = leftArgs[index].isDefEq(rightArgs[index], localCtxLeft, localCtxRight)
        if (!argumentMatches) {
            return false
        }
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
    val unfoldedExpr = when (this) {
        is Expression.Proj -> this.whnfCore(localCtx, cheapProjection = false).takeIf { it !== this }
        else -> this.tryUnfoldSpineHeadOnce()
    } ?: return null
    if (unfoldedExpr == this) return null
    return LazyDeltaStep(
        unfoldedExpr = unfoldedExpr,
        kind = headStep.kind,
        regularHeight = headStep.regularHeight,
    )
}

context(env: Environment)
private fun Expression.Proj.tryReduceProjectionHeadOnce(): Expression? {
    val reducedStructExpr = when (val structExpr = this.structExpr) {
        is Expression.App -> structExpr.tryReduceProjectionApp()
            ?: structExpr.tryUnfoldSpineHeadOnce()

        is Expression.Proj -> structExpr.tryReduceProjectionHeadOnce()
        else -> structExpr.tryUnfoldReducibleHeadOnce()
    } ?: return null

    val iotaStructExpr = reducedStructExpr.tryStringLitCtor() ?: reducedStructExpr
    val [headExpr, args] = iotaStructExpr.unfoldApp()
    val ctorConst = headExpr as? Expression.Const
    val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
    if (
        ctorDecl != null &&
        ctorDecl.inductName == this.typeNameExpr &&
        this.projIndex in 0 until ctorDecl.numFields &&
        args.size == ctorDecl.numParams + ctorDecl.numFields
    ) {
        return args[ctorDecl.numParams + this.projIndex]
    }
    return env.addCustomExpr {
        Expression.Proj(
            typeName = this@tryReduceProjectionHeadOnce.typeNameIndex,
            idx = this@tryReduceProjectionHeadOnce.projIndex,
            struct = reducedStructExpr.ie,
            ie = it,
        )
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
        if (originalHead is Expression.Proj) {
            return originalHead.tryReduceProjectionHeadOnce()?.applyArgs(originalArgs)
        }

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
private fun Expression.sameShape(other: Expression): Boolean {
    data class Frame(val left: Expression, val right: Expression, val expanded: Boolean)

    fun cacheKey(left: Expression, right: Expression): Long {
        val leftId = left.ie
        val rightId = right.ie
        return if (leftId <= rightId) {
            (leftId.toLong() shl 32) xor (rightId.toLong() and 0xffffffffL)
        } else {
            (rightId.toLong() shl 32) xor (leftId.toLong() and 0xffffffffL)
        }
    }

    val rootKey = cacheKey(this, other)
    env.sameShapeCache[rootKey]?.let { return it }
    val stack = ArrayDeque<Frame>()
    stack.addLast(Frame(this, other, false))
    while (stack.isNotEmpty()) {
        val frame = stack.removeLast()
        val key = cacheKey(frame.left, frame.right)
        env.sameShapeCache[key]?.let { cached ->
            if (!cached) {
                env.sameShapeCache[rootKey] = false
                return false
            }
            continue
        }
        if (frame.expanded || frame.left.ie == frame.right.ie) {
            env.sameShapeCache[key] = true
            continue
        }

        val children = mutableListOf<Pair<Expression, Expression>>()
        val headsMatch = when {
            frame.left is Expression.Bvar && frame.right is Expression.Bvar ->
                frame.left.bvar == frame.right.bvar

            frame.left is Expression.NatVal && frame.right is Expression.NatVal ->
                frame.left.natVal == frame.right.natVal

            frame.left is Expression.StrVal && frame.right is Expression.StrVal ->
                frame.left.strVal == frame.right.strVal

            frame.left is Expression.Sort && frame.right is Expression.Sort ->
                frame.left.level == frame.right.level

            frame.left is Expression.Const && frame.right is Expression.Const ->
                frame.left.name == frame.right.name &&
                        frame.left.levels.size == frame.right.levels.size &&
                        frame.left.levels.zip(frame.right.levels).all { it.first == it.second }

            frame.left is Expression.App && frame.right is Expression.App -> {
                children += frame.left.fnExpr to frame.right.fnExpr
                children += frame.left.argExpr to frame.right.argExpr
                true
            }

            frame.left is Expression.ForallE && frame.right is Expression.ForallE -> {
                children += frame.left.typeExpr to frame.right.typeExpr
                children += frame.left.bodyExpr to frame.right.bodyExpr
                true
            }

            frame.left is Expression.Lam && frame.right is Expression.Lam -> {
                children += frame.left.typeExpr to frame.right.typeExpr
                children += frame.left.bodyExpr to frame.right.bodyExpr
                true
            }

            frame.left is Expression.LetE && frame.right is Expression.LetE -> {
                children += frame.left.typeExpr to frame.right.typeExpr
                children += frame.left.valueExpr to frame.right.valueExpr
                children += frame.left.bodyExpr to frame.right.bodyExpr
                true
            }

            frame.left is Expression.Mdata && frame.right is Expression.Mdata -> {
                children += frame.left.expr to frame.right.expr
                true
            }

            frame.left is Expression.Proj && frame.right is Expression.Proj -> {
                if (
                    frame.left.typeNameExpr != frame.right.typeNameExpr ||
                    frame.left.projIndex != frame.right.projIndex
                ) {
                    false
                } else {
                    children += frame.left.structExpr to frame.right.structExpr
                    true
                }
            }

            else -> false
        }
        if (!headsMatch) {
            env.sameShapeCache[key] = false
            env.sameShapeCache[rootKey] = false
            return false
        }
        if (children.isEmpty()) {
            env.sameShapeCache[key] = true
        } else {
            stack.addLast(Frame(frame.left, frame.right, true))
            children.asReversed().forEach { childPair ->
                stack.addLast(Frame(childPair.first, childPair.second, false))
            }
        }
    }
    env.sameShapeCache[rootKey] = true
    return true
}

context(env: Environment)
private fun Expression.isDefEqWhnf(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val result = when (this) {
        is Expression.App if other is Expression.App ->
            this.isDefEqWhnfSpine(other, localCtxLeft, localCtxRight)

        is Expression.Bvar if other is Expression.Bvar -> {
            this.bvar == other.bvar
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
                        env.consLocalCtx(this.typeExpr, localCtxLeft),
                        env.consLocalCtx(other.typeExpr, localCtxRight),
                    )
        }

        is Expression.Lam if other is Expression.Lam -> {
            this.typeExpr.isDefEq(other.typeExpr, localCtxLeft, localCtxRight) &&
                    this.bodyExpr.isDefEq(
                        other.bodyExpr,
                        env.consLocalCtx(this.typeExpr, localCtxLeft),
                        env.consLocalCtx(other.typeExpr, localCtxRight),
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
            val reducedThis = this.reduce(localCtx = localCtxLeft)
            val reducedOther = other.reduce(localCtx = localCtxRight)
            if (reducedThis == this && reducedOther == other) {
                false
            } else {
                reducedThis.isDefEq(reducedOther, localCtxLeft, localCtxRight)
            }
        }
    }
    return result ||
            (this.canBeStructureLikeValue() &&
                    other.canBeStructureLikeValue() &&
                    this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight))
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
        (this.inferType(localCtx = localCtxLeft).whnf(localCtx = localCtxLeft) as? Expression.ForallE)?.typeExpr
            ?: return null
    }
    val rightDomain = if (rightLam != null) {
        rightLam.typeExpr
    } else {
        (other.inferType(localCtx = localCtxRight).whnf(localCtx = localCtxRight) as? Expression.ForallE)?.typeExpr
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
    return leftUnderBinder.isDefEq(
        rightUnderBinder,
        env.consLocalCtx(leftDomain, localCtxLeft),
        env.consLocalCtx(rightDomain, localCtxRight),
    )
}

context(env: Environment)
private fun Expression.tryCompareWithKnownFunctionType(
    other: Expression,
    leftDomain: Expression,
    rightDomain: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftReduced = this.reduce(localCtx = localCtxLeft)
    val rightReduced = other.reduce(localCtx = localCtxRight)
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
        env.consLocalCtx(leftDomain, localCtxLeft),
        env.consLocalCtx(rightDomain, localCtxRight),
    )
}

context(env: Environment)
private fun Expression.isEtaComparableStructureType(localCtx: List<Expression>): Boolean {
    val [typeHead, _] = this.unfoldApp()
    val typeConst = typeHead as? Expression.Const ?: return false
    val typeNameIndex = env.nameIndices[typeConst.name] ?: return false
    val structureDecl = env.declarations[typeNameIndex] as? Inductive.InductiveVal ?: return false
    if (structureDecl.isRec || structureDecl.ctors.size != 1 || structureDecl.numIndices != 0) {
        return false
    }
    return !this.inferSort(localCtx = localCtx).isLessOrEqual(Level.Zero)
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

private sealed interface InferFrame {
    data class Cache(val key: InferTypeCacheKey, val ownsSlot: Boolean) : InferFrame

    data class AppFunction(
        val app: Expression.App,
        val args: List<Expression>,
        val levelSubst: Map<Int, Level>,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class AppArgument(
        val app: Expression.App,
        val args: List<Expression>,
        val index: Int,
        val functionType: Expression.ForallE,
        val argument: Expression,
        val levelSubst: Map<Int, Level>,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class ForallDomain(
        val expression: Expression.ForallE,
        val levelSubst: Map<Int, Level>,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class ForallBody(
        val expression: Expression.ForallE,
        val domainSort: Level,
        val bodyCtx: List<Expression>,
    ) : InferFrame

    data class LambdaDomain(
        val expression: Expression.Lam,
        val levelSubst: Map<Int, Level>,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class LambdaBody(val expression: Expression.Lam) : InferFrame

    data class LetType(
        val expression: Expression.LetE,
        val levelSubst: Map<Int, Level>,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class LetValue(
        val expression: Expression.LetE,
        val value: Expression,
        val expectedType: Expression,
        val levelSubst: Map<Int, Level>,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class Projection(
        val expression: Expression.Proj,
        val localCtx: List<Expression>,
    ) : InferFrame
}

context(env: Environment)
private fun requireSort(type: Expression, subject: Expression, localCtx: List<Expression>): Level {
    val typeWhnf = type.whnf(localCtx = localCtx)
    val sort = typeWhnf as? Expression.Sort
        ?: error("Expected Sort type for ${subject.toStringDetailed()}, got ${typeWhnf.toStringDetailed()}")
    return sort.level
}

context(env: Environment)
fun Expression.inferType(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList()
): Expression {
    val frames = ArrayDeque<InferFrame>()
    val ownedCacheSlots = mutableSetOf<InferTypeCacheKey>()
    var currentExpr = this
    var currentLevelSubst = levelSubst
    var currentLocalCtx = localCtx
    var result: Expression = this
    var evaluating = true

    try {
        while (true) {
            if (evaluating) {
                val cacheKey = if (currentLevelSubst.isEmpty()) {
                    InferTypeCacheKey(currentExpr.ie, env.localCtxId(currentLocalCtx))
                } else {
                    null
                }
                if (cacheKey != null) {
                    val cachedType = env.inferTypeCacheNoLevelSubst[cacheKey]
                    if (cachedType != null) {
                        env.inferTypeCacheHits += 1
                        result = cachedType
                        evaluating = false
                        continue
                    }
                    val ownsSlot = env.inferTypeInProgress.add(cacheKey)
                    if (ownsSlot) ownedCacheSlots += cacheKey
                    frames.addLast(InferFrame.Cache(cacheKey, ownsSlot))
                }

                when (val expr = currentExpr) {
                    is Expression.App -> {
                        val appSpine = expr.unfoldApp()
                        val headExpr = appSpine.first
                        val args = appSpine.second
                        frames.addLast(InferFrame.AppFunction(expr, args, currentLevelSubst, currentLocalCtx))
                        currentExpr = headExpr
                    }

                    is Expression.Bvar -> {
                        result = if (expr.bvar < currentLocalCtx.size) {
                            // live binder: its stored type was recorded outside this binder,
                            // so lift it back under the current live-binder depth.
                            currentLocalCtx[expr.bvar].lift(expr.bvar + 1)
                                .instantiateLevelParams(currentLevelSubst)
                        } else {
                            error("Unbound bvar ${expr.bvar} in ${expr.toStringDetailed()}")
                        }
                        evaluating = false
                    }

                    is Expression.Const -> {
                        val type = env.declTypeByName[expr.name]
                            ?: error("Declaration not found for ${expr.name}")
                        result = type.instantiateLevelParams(expr.composeLevelSubst(currentLevelSubst))
                        evaluating = false
                    }

                    is Expression.ForallE -> {
                        frames.addLast(InferFrame.ForallDomain(expr, currentLevelSubst, currentLocalCtx))
                        currentExpr = expr.typeExpr
                    }

                    is Expression.Lam -> {
                        frames.addLast(InferFrame.LambdaDomain(expr, currentLevelSubst, currentLocalCtx))
                        currentExpr = expr.typeExpr
                    }

                    is Expression.Sort -> {
                        val normalizedLevel = expr.level.instantiateLevelParams(currentLevelSubst)
                        val newLevel = env.addCustomSuccLevel(normalizedLevel.il)
                        result = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
                        evaluating = false
                    }

                    is Expression.LetE -> {
                        frames.addLast(InferFrame.LetType(expr, currentLevelSubst, currentLocalCtx))
                        currentExpr = expr.typeExpr
                    }

                    is Expression.Mdata -> currentExpr = expr.expr

                    is Expression.NatVal -> {
                        val natTypeIndex = env.findRootInductive("Nat")?.first
                            ?: error("Nat literal ${expr.natVal} used without Nat inductive in environment")
                        result = env.addCustomExpr {
                            Expression.Const(_name = natTypeIndex, us = emptyList(), ie = it)
                        }
                        evaluating = false
                    }

                    is Expression.Proj -> {
                        frames.addLast(InferFrame.Projection(expr, currentLocalCtx))
                        currentExpr = expr.structExpr
                    }

                    is Expression.StrVal -> {
                        val stringTypeIndex = env.findRootInductive("String")?.first
                            ?: error("String literal used without String inductive in environment")
                        result = env.addCustomExpr {
                            Expression.Const(_name = stringTypeIndex, us = emptyList(), ie = it)
                        }
                        evaluating = false
                    }
                }
                continue
            }

            if (frames.isEmpty()) return result
            when (val frame = frames.removeLast()) {
                is InferFrame.Cache -> {
                    if (frame.ownsSlot) {
                        env.inferTypeCacheNoLevelSubst[frame.key] = result
                        env.inferTypeInProgress.remove(frame.key)
                        ownedCacheSlots.remove(frame.key)
                    }
                }

                is InferFrame.AppFunction -> {
                    val functionType = result.whnf(localCtx = frame.localCtx) as? Expression.ForallE
                        ?: error("Expected function type for app ${frame.app.toStringDetailed()}, got ${result.toStringDetailed()}")
                    val argument = frame.args.first().instantiateLevelParams(frame.levelSubst)
                    frames.addLast(
                        InferFrame.AppArgument(
                            frame.app,
                            frame.args,
                            0,
                            functionType,
                            argument,
                            frame.levelSubst,
                            frame.localCtx,
                        )
                    )
                    currentExpr = argument
                    currentLevelSubst = emptyMap()
                    currentLocalCtx = frame.localCtx
                    evaluating = true
                }

                is InferFrame.AppArgument -> {
                    val argumentTypeMatches =
                        frame.functionType.typeExpr.isDefEq(result, frame.localCtx, frame.localCtx)
                    check(argumentTypeMatches) {
                        "Application argument type mismatch in app ${frame.app.toStringDetailed()}: expected ${frame.functionType.typeExpr.toStringDetailed()}, got ${result.toStringDetailed()}"
                    }
                    val nextFunctionType = frame.functionType.bodyExpr.applySubst(listOf(frame.argument))
                    val nextIndex = frame.index + 1
                    if (nextIndex == frame.args.size) {
                        result = nextFunctionType
                    } else {
                        val functionType = nextFunctionType.whnf(localCtx = frame.localCtx) as? Expression.ForallE
                            ?: error("Expected function type for app ${frame.app.toStringDetailed()}, got ${nextFunctionType.toStringDetailed()}")
                        val argument = frame.args[nextIndex].instantiateLevelParams(frame.levelSubst)
                        frames.addLast(
                            InferFrame.AppArgument(
                                frame.app,
                                frame.args,
                                nextIndex,
                                functionType,
                                argument,
                                frame.levelSubst,
                                frame.localCtx,
                            )
                        )
                        currentExpr = argument
                        currentLevelSubst = emptyMap()
                        currentLocalCtx = frame.localCtx
                        evaluating = true
                    }
                }

                is InferFrame.ForallDomain -> {
                    val domainSort = requireSort(result, frame.expression.typeExpr, frame.localCtx)
                    val bodyCtx = env.consLocalCtx(frame.expression.typeExpr, frame.localCtx)
                    frames.addLast(InferFrame.ForallBody(frame.expression, domainSort, bodyCtx))
                    currentExpr = frame.expression.bodyExpr
                    currentLevelSubst = frame.levelSubst
                    currentLocalCtx = bodyCtx
                    evaluating = true
                }

                is InferFrame.ForallBody -> {
                    val bodySort = requireSort(result, frame.expression.bodyExpr, frame.bodyCtx)
                    val resultLevel = env.addCustomImaxLevel(frame.domainSort.il, bodySort.il)
                    result = env.addCustomExpr { Expression.Sort(resultLevel.il, it) }
                }

                is InferFrame.LambdaDomain -> {
                    requireSort(result, frame.expression.typeExpr, frame.localCtx)
                    frames.addLast(InferFrame.LambdaBody(frame.expression))
                    currentExpr = frame.expression.bodyExpr
                    currentLevelSubst = frame.levelSubst
                    currentLocalCtx = env.consLocalCtx(frame.expression.typeExpr, frame.localCtx)
                    evaluating = true
                }

                is InferFrame.LambdaBody -> {
                    result = env.addCustomExpr {
                        frame.expression.copyAsForAllE().copy(body = result.ie, ie = it)
                    }
                }

                is InferFrame.LetType -> {
                    requireSort(result, frame.expression.typeExpr, frame.localCtx)
                    val expectedType = frame.expression.typeExpr.instantiateLevelParams(frame.levelSubst)
                    val value = frame.expression.valueExpr.instantiateLevelParams(frame.levelSubst)
                    frames.addLast(
                        InferFrame.LetValue(
                            frame.expression,
                            value,
                            expectedType,
                            frame.levelSubst,
                            frame.localCtx,
                        )
                    )
                    currentExpr = value
                    currentLevelSubst = emptyMap()
                    currentLocalCtx = frame.localCtx
                    evaluating = true
                }

                is InferFrame.LetValue -> {
                    check(frame.expectedType.isDefEq(result, frame.localCtx, frame.localCtx)) {
                        "Let value type mismatch in ${frame.expression.toStringDetailed()}: expected ${frame.expectedType.toStringDetailed()}, got ${result.toStringDetailed()}"
                    }
                    currentExpr = frame.expression.bodyExpr.applySubst(listOf(frame.value))
                    currentLevelSubst = frame.levelSubst
                    currentLocalCtx = frame.localCtx
                    evaluating = true
                }

                is InferFrame.Projection -> {
                    result = frame.expression.inferProjectionType(result, frame.localCtx)
                }
            }
        }
    } finally {
        ownedCacheSlots.forEach { env.inferTypeInProgress.remove(it) }
    }
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
            val natReducedExpr = this.tryReduceNatLiteral(levelSubst, localCtx)
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
        env.whnfCacheNoLevelSubst[this.ie]?.let { return it }
    } else if (cacheKey != null) {
        env.whnfCacheWithCtxNoLevelSubst[cacheKey]?.let { return it }
    }
    var current = this.instantiateLevelParams(levelSubst)
    val result: Expression
    while (true) {
        val next = current.tryWhnfStep(localCtx)
        if (next == null || next == current) {
            result = current
            break
        }
        current = next
    }
    if (cacheKey == null && levelSubst.isEmpty()) {
        env.whnfCacheNoLevelSubst[this.ie] = result
    } else if (cacheKey != null) {
        env.whnfCacheWithCtxNoLevelSubst[cacheKey] = result
    }
    return result
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
        this.tryReduceNatLiteral(emptyMap(), localCtx)?.let { return it }
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
        val spine = structExpr.unfoldApp()
        val ctorConst = spine.first as? Expression.Const
        val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
        if (
            ctorDecl != null &&
            ctorDecl.inductName == this.typeNameExpr &&
            this.projIndex in 0 until ctorDecl.numFields &&
            spine.second.size == ctorDecl.numParams + ctorDecl.numFields
        ) {
            spine.second[ctorDecl.numParams + this.projIndex]
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

    else -> null
}

private enum class WhnfMode { CoreCheapProjection, CoreFullProjection, Full }

private sealed interface WhnfFrame {
    data class FinishFull(val original: Expression) : WhnfFrame
    data class ApplyHead(
        val app: Expression.App,
        val originalHead: Expression,
        val args: List<Expression>,
        val mode: WhnfMode,
    ) : WhnfFrame

    data class ReduceProjection(val projection: Expression.Proj, val mode: WhnfMode) : WhnfFrame
    data class ReduceRecursor(val app: Expression.App, val mode: WhnfMode) : WhnfFrame
    data class ReduceQuot(val app: Expression.App, val mode: WhnfMode) : WhnfFrame
    data class ReduceNatPrimitive(
        val app: Expression.App,
        val args: List<Expression>,
        val values: List<NatValue>,
        val nextIndex: Int,
        val finishFrame: FinishFull,
    ) : WhnfFrame
}

context(env: Environment)
private fun Expression.whnfCore(
    localCtx: List<Expression>,
    cheapProjection: Boolean,
): Expression = this.normalizeWhnf(
    localCtx,
    if (cheapProjection) WhnfMode.CoreCheapProjection else WhnfMode.CoreFullProjection,
)

context(env: Environment)
private fun Expression.normalizeWhnf(localCtx: List<Expression>, initialMode: WhnfMode): Expression {
    val frames = ArrayDeque<WhnfFrame>()
    var current = this
    var mode = initialMode
    var result: Expression? = null
    while (true) {
        if (result == null) {
            when (mode) {
                WhnfMode.Full -> {
                    val cached = current.cachedWhnf(localCtx)
                    if (cached != null) {
                        result = cached
                    } else {
                        frames.addLast(WhnfFrame.FinishFull(current))
                        mode = WhnfMode.CoreFullProjection
                    }
                }

                WhnfMode.CoreCheapProjection, WhnfMode.CoreFullProjection -> when (current) {
                    is Expression.Mdata -> current = current.expr
                    is Expression.LetE -> current = current.bodyExpr.applySubst(listOf(current.valueExpr))
                    is Expression.Proj -> {
                        frames.addLast(WhnfFrame.ReduceProjection(current, mode))
                        current = current.structExpr
                        mode = if (mode == WhnfMode.CoreCheapProjection) {
                            WhnfMode.CoreCheapProjection
                        } else {
                            WhnfMode.Full
                        }
                    }

                    is Expression.App -> {
                        val spine = current.unfoldApp()
                        frames.addLast(WhnfFrame.ApplyHead(current, spine.first, spine.second, mode))
                        current = spine.first
                    }

                    else -> result = current
                }
            }
            continue
        }

        if (frames.isEmpty()) return result
        when (val frame = frames.removeLast()) {
            is WhnfFrame.FinishFull -> {
                val primitiveApp = result as? Expression.App
                val primitiveArgs = primitiveApp?.natLiteralPrimitiveArgsOrNull()
                if (primitiveApp != null && primitiveArgs != null) {
                    frames.addLast(
                        WhnfFrame.ReduceNatPrimitive(
                            app = primitiveApp,
                            args = primitiveArgs,
                            values = emptyList(),
                            nextIndex = 0,
                            finishFrame = frame,
                        )
                    )
                    current = primitiveArgs.first()
                    mode = WhnfMode.Full
                    result = null
                } else {
                    val unfolded = result.unfoldDefinitionOnce()
                    if (unfolded == null) frame.original.cacheWhnf(localCtx, result)
                    else {
                        frames.addLast(frame)
                        current = unfolded
                        mode = WhnfMode.CoreFullProjection
                        result = null
                    }
                }
            }

            is WhnfFrame.ReduceNatPrimitive -> {
                val value = result.asNatLiteralValue()
                if (value == null) {
                    val unfolded = frame.app.unfoldDefinitionOnce()
                    if (unfolded == null) {
                        result = frame.app
                        frame.finishFrame.original.cacheWhnf(localCtx, result)
                    } else {
                        frames.addLast(frame.finishFrame)
                        current = unfolded
                        mode = WhnfMode.CoreFullProjection
                        result = null
                    }
                } else {
                    val values = frame.values + value
                    val nextIndex = frame.nextIndex + 1
                    if (nextIndex < frame.args.size) {
                        frames.addLast(frame.copy(values = values, nextIndex = nextIndex))
                        current = frame.args[nextIndex]
                        mode = WhnfMode.Full
                        result = null
                    } else {
                        val reduced = frame.app.reduceNatLiteralValues(values)
                        if (reduced == null) {
                            val unfolded = frame.app.unfoldDefinitionOnce()
                            if (unfolded == null) {
                                result = frame.app
                                frame.finishFrame.original.cacheWhnf(localCtx, result)
                            } else {
                                frames.addLast(frame.finishFrame)
                                current = unfolded
                                mode = WhnfMode.CoreFullProjection
                                result = null
                            }
                        } else {
                            result = reduced
                            frame.finishFrame.original.cacheWhnf(localCtx, result)
                        }
                    }
                }
            }

            is WhnfFrame.ReduceProjection -> {
                val reduced = frame.projection.reduceProjectionCore(result)
                if (reduced == null) {
                    result = frame.projection
                } else {
                    current = reduced
                    mode = frame.mode
                    result = null
                }
            }

            is WhnfFrame.ApplyHead -> {
                var head = result
                var consumedArgs = 0
                while (head is Expression.Lam && consumedArgs < frame.args.size) {
                    head = head.bodyExpr.applySubst(listOf(frame.args[consumedArgs]))
                    consumedArgs += 1
                }
                if (consumedArgs > 0 || head !== frame.originalHead) {
                    current = head.applyArgs(frame.args.drop(consumedArgs))
                    mode = frame.mode
                    result = null
                } else {
                    val recursorMajor = frame.app.recursorMajorOrNull()
                    val quotMajor = if (recursorMajor == null) frame.app.quotMajorOrNull() else null
                    when {
                        recursorMajor != null -> {
                            frames.addLast(WhnfFrame.ReduceRecursor(frame.app, frame.mode))
                            current = recursorMajor
                            mode = WhnfMode.Full
                            result = null
                        }

                        quotMajor != null -> {
                            frames.addLast(WhnfFrame.ReduceQuot(frame.app, frame.mode))
                            current = quotMajor
                            mode = WhnfMode.Full
                            result = null
                        }

                        else -> result = frame.app
                    }
                }
            }

            is WhnfFrame.ReduceRecursor -> {
                val reduced = frame.app.tryReduceRecursorHead(emptyMap(), localCtx, result)
                if (reduced == null) {
                    result = frame.app
                } else {
                    current = reduced
                    mode = frame.mode
                    result = null
                }
            }

            is WhnfFrame.ReduceQuot -> {
                val reduced = frame.app.tryReduceQuotHead(emptyMap(), localCtx, result)
                if (reduced == null) {
                    result = frame.app
                } else {
                    current = reduced
                    mode = frame.mode
                    result = null
                }
            }
        }
    }
}

context(env: Environment)
private fun Expression.cachedWhnf(localCtx: List<Expression>): Expression? =
    if (localCtx.isEmpty()) {
        env.whnfCacheNoLevelSubst[this.ie]
    } else {
        env.whnfCacheWithCtxNoLevelSubst[ReduceCacheKey(this.ie, env.localCtxId(localCtx))]
    }

context(env: Environment)
private fun Expression.cacheWhnf(localCtx: List<Expression>, result: Expression) {
    if (localCtx.isEmpty()) {
        env.whnfCacheNoLevelSubst[this.ie] = result
    } else {
        env.whnfCacheWithCtxNoLevelSubst[ReduceCacheKey(this.ie, env.localCtxId(localCtx))] = result
    }
}

context(env: Environment)
private fun Expression.Proj.reduceProjectionCore(normalizedStruct: Expression): Expression? {
    val struct = normalizedStruct.tryStringLitCtor() ?: normalizedStruct
    val spine = struct.unfoldApp()
    val constructor = (spine.first as? Expression.Const)?.decl as? Inductive.ConstructorVal ?: return null
    if (constructor.inductName != this.typeNameExpr || this.projIndex !in 0 until constructor.numFields) return null
    val fieldIndex = constructor.numParams + this.projIndex
    return spine.second.getOrNull(fieldIndex)
}

context(env: Environment)
private fun Expression.App.recursorMajorOrNull(): Expression? {
    val spine = this.unfoldApp()
    val recursor = (spine.first as? Expression.Const)?.decl as? Inductive.RecursorVal ?: return null
    val majorIndex = recursor.numParams + recursor.numMotives + recursor.numMinors + recursor.numIndices
    return spine.second.getOrNull(majorIndex)
}

context(env: Environment)
private fun Expression.App.quotMajorOrNull(): Expression? {
    val spine = this.unfoldApp()
    val quot = (spine.first as? Expression.Const)?.decl as? Declaration.Quot ?: return null
    if (quot.kind != Declaration.Quot.Kind.Lift && quot.kind != Declaration.Quot.Kind.Ind) return null
    val arity = quot.typeExpr.forallBinderCount()
    if (spine.second.size < arity) return null
    return spine.second[arity - 1]
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
private fun Expression.tryNatLiteralDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val leftNat = this.tryRecognizeNatLiteralCore(localCtxLeft)
    val rightNat = other.tryRecognizeNatLiteralCore(localCtxRight)
    if (leftNat != null && rightNat != null) return leftNat == rightNat
    if (leftNat != null) {
        val reducedRight = (other as? Expression.App)
            ?.tryReduceNatLiteral(emptyMap(), localCtxRight, normalizeOperands = true)
        return reducedRight?.asNatLiteralValue() == leftNat
    }
    if (rightNat != null) {
        val reducedLeft = (this as? Expression.App)
            ?.tryReduceNatLiteral(emptyMap(), localCtxLeft, normalizeOperands = true)
        return reducedLeft?.asNatLiteralValue() == rightNat
    }
    return false
}

context(env: Environment)
private fun Expression.asNatLiteralValue(): NatValue? = when (this) {
    is Expression.NatVal -> this.natVal
    else -> if (this.isNatZeroCtorConst()) NatValue.ZERO else null
}

context(env: Environment)
private fun Expression.tryRecognizeNatLiteral(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
): NatValue? {
    if (levelSubst.isNotEmpty()) {
        return this.instantiateLevelParams(levelSubst).tryRecognizeNatLiteral(emptyMap(), localCtx)
    }
    val cacheKey = ReduceCacheKey(this.ie, env.localCtxId(localCtx))
    if (env.natLiteralCacheNoLevelSubst.containsKey(cacheKey)) {
        return env.natLiteralCacheNoLevelSubst[cacheKey]
    }

    env.natLiteralRecognitionDepth += 1
    val result = try {
        this.tryRecognizeNatLiteralByWhnf(localCtx)
    } finally {
        env.natLiteralRecognitionDepth -= 1
    }

    env.natLiteralCacheNoLevelSubst[cacheKey] = result
    return result
}

context(env: Environment)
private fun Expression.tryRecognizeNatLiteralCore(localCtx: List<Expression>): NatValue? {
    var current = this
    var succOffset = NatValue.ZERO
    while (true) {
        when (current) {
            is Expression.Mdata -> current = current.expr
            is Expression.LetE -> current = current.bodyExpr.applySubst(listOf(current.valueExpr))
            else -> {
                val baseValue = current.asNatLiteralValue()
                if (baseValue != null) return baseValue + succOffset

                val appExpr = current as? Expression.App ?: return null
                val [headExpr, args] = appExpr.unfoldApp()
                val headConst = headExpr as? Expression.Const ?: return null

                fun natArg(index: Int): NatValue? = args.getOrNull(index)?.tryRecognizeNatLiteral(emptyMap(), localCtx)

                val value = when (headConst.name.toStringDetailed()) {
                    "Nat.succ" -> {
                        current = args.getOrNull(0) ?: return null
                        succOffset += NatValue.ONE
                        continue
                    }

                    "Nat.add" -> {
                        val lhs = natArg(0) ?: return null
                        val rhs = natArg(1) ?: return null
                        lhs + rhs
                    }

                    "Nat.sub" -> {
                        val lhs = natArg(0) ?: return null
                        val rhs = natArg(1) ?: return null
                        if (lhs >= rhs) lhs - rhs else NatValue.ZERO
                    }

                    "Nat.mul" -> {
                        val lhs = natArg(0) ?: return null
                        val rhs = natArg(1) ?: return null
                        lhs * rhs
                    }

                    "Nat.pow" -> {
                        val base = natArg(0) ?: return null
                        val exponent = natArg(1)?.toIntOrNull() ?: return null
                        base.pow(exponent)
                    }

                    "Nat.div" -> {
                        val lhs = natArg(0) ?: return null
                        val rhs = natArg(1) ?: return null
                        lhs.divLean(rhs)
                    }

                    "Nat.mod" -> {
                        val lhs = natArg(0) ?: return null
                        val rhs = natArg(1) ?: return null
                        lhs.modLean(rhs)
                    }

                    else -> return null
                }
                return value + succOffset
            }
        }
    }
}

context(env: Environment)
private fun Expression.tryRecognizeNatLiteralByWhnf(
    localCtx: List<Expression>,
): NatValue? {
    val normalizedExpr = when (this) {
        is Expression.App -> {
            val headConst = this.unfoldApp().first as? Expression.Const
            if (headConst?.projectionReductionInfo() != null) this.whnf(localCtx = localCtx) else this
        }

        is Expression.Const,
        is Expression.LetE,
        is Expression.Mdata -> this.whnf(localCtx = localCtx)

        else -> this
    }
    return normalizedExpr.asNatLiteralValue() ?: run {
        val appExpr = normalizedExpr as? Expression.App ?: return@run null
        val [headExpr, args] = appExpr.unfoldApp()
        val headConst = headExpr as? Expression.Const ?: return@run null

        fun natArg(index: Int): NatValue? = args.getOrNull(index)?.tryRecognizeNatLiteral(emptyMap(), localCtx)

        when (headConst.name.toStringDetailed()) {
            "Nat.succ" -> natArg(0)?.plus(NatValue.ONE)
            "Nat.add" -> {
                val lhs = natArg(0) ?: return@run null
                val rhs = natArg(1) ?: return@run null
                lhs + rhs
            }

            "Nat.sub" -> {
                val lhs = natArg(0) ?: return@run null
                val rhs = natArg(1) ?: return@run null
                if (lhs >= rhs) lhs - rhs else NatValue.ZERO
            }

            "Nat.mul" -> {
                val lhs = natArg(0) ?: return@run null
                val rhs = natArg(1) ?: return@run null
                lhs * rhs
            }

            "Nat.pow" -> {
                val base = natArg(0) ?: return@run null
                val exponent = natArg(1)?.toIntOrNull() ?: return@run null
                base.pow(exponent)
            }

            "Nat.div" -> {
                val lhs = natArg(0) ?: return@run null
                val rhs = natArg(1) ?: return@run null
                lhs.divLean(rhs)
            }

            "Nat.mod" -> {
                val lhs = natArg(0) ?: return@run null
                val rhs = natArg(1) ?: return@run null
                lhs.modLean(rhs)
            }

            else -> null
        }
    }
}

context(env: Environment)
private fun Expression.isNatLiteralPrimitiveConst(): Boolean = when (this) {
    is Expression.Const -> when (this.name.toStringDetailed()) {
        "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.div", "Nat.mod",
        "Nat.beq", "Nat.ble" -> true

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
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.div", "Nat.mod", "Nat.beq",
        "Nat.ble" -> 2

        else -> null
    }
}

context(env: Environment)
private fun Expression.App.natLiteralPrimitiveArgsOrNull(): List<Expression>? {
    val spine = this.unfoldApp()
    val arity = this.natLiteralPrimitiveArity() ?: return null
    return spine.second.takeIf { it.size == arity }
}

context(env: Environment)
private fun Expression.App.reduceNatLiteralValues(values: List<NatValue>): Expression? {
    val head = this.unfoldApp().first as? Expression.Const ?: return null
    return when (head.name.toStringDetailed()) {
        "Nat.succ" -> env.addCustomExpr { Expression.NatVal(values[0] + NatValue.ONE, it) }
        "Nat.add" -> env.addCustomExpr { Expression.NatVal(values[0] + values[1], it) }
        "Nat.sub" -> env.addCustomExpr {
            Expression.NatVal(if (values[0] >= values[1]) values[0] - values[1] else NatValue.ZERO, it)
        }

        "Nat.mul" -> env.addCustomExpr { Expression.NatVal(values[0] * values[1], it) }
        "Nat.pow" -> {
            val exponent = values[1].toIntOrNull() ?: return null
            env.addCustomExpr { Expression.NatVal(values[0].pow(exponent), it) }
        }

        "Nat.div" -> env.addCustomExpr { Expression.NatVal(values[0].divLean(values[1]), it) }
        "Nat.mod" -> env.addCustomExpr { Expression.NatVal(values[0].modLean(values[1]), it) }
        "Nat.beq" -> boolCtor(values[0] == values[1])
        "Nat.ble" -> boolCtor(values[0] <= values[1])
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
private fun Expression.App.tryReduceNatLiteral(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
    normalizeOperands: Boolean = true,
): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val headConst = headExpr as? Expression.Const ?: return null

    fun natArg(index: Int): NatValue? {
        val argExpr = args.getOrNull(index) ?: return null
        return if (normalizeOperands) {
            argExpr.instantiateLevelParams(levelSubst)
                .normalizeWhnf(localCtx, WhnfMode.Full)
                .asNatLiteralValue()
        } else {
            argExpr.tryRecognizeNatLiteral(levelSubst, localCtx)
        }
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
private fun Expression.Proj.inferProjectionType(structType0: Expression, localCtx: List<Expression>): Expression {
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

    fun tryReduceKRule(): Expression? {
        if (!recursorDecl.k) return null
        val kRule = recursorDecl.rules.singleOrNull() ?: return null
        if (kRule.nfields != 0) return null
        val kCtorDecl = env.constructorByName[kRule.ctorName] ?: return null
        if (kCtorDecl.numFields != 0 || kCtorDecl.numParams != recursorDecl.numParams) return null
        val indexArgs = args.drop(recursorArgsPrefixSize).take(recursorDecl.numIndices)
        if (indexArgs.size != recursorDecl.numIndices) return null

        var ctorTail: Expression = kCtorDecl.typeExpr.instantiateLevelParams(recursorLevelSubst)
        repeat(kCtorDecl.numParams + kCtorDecl.numFields) { binderIndex ->
            val ctorForall = ctorTail as? Expression.ForallE ?: return null
            val binderArg = if (binderIndex < kCtorDecl.numParams) {
                args[binderIndex].instantiateLevelParams(levelSubst)
            } else {
                return null
            }
            ctorTail = ctorForall.bodyExpr.applySubst(listOf(binderArg))
        }

        val [ctorResultHead, ctorResultArgs] = ctorTail.unfoldApp()
        val ctorResultConst = ctorResultHead as? Expression.Const ?: return null
        if (ctorResultConst.name != kCtorDecl.inductName) return null
        if (ctorResultArgs.size != recursorDecl.numParams + recursorDecl.numIndices) return null
        val expectedIndexArgs = ctorResultArgs.drop(recursorDecl.numParams)
        repeat(recursorDecl.numIndices) { index ->
            val expectedIndex = expectedIndexArgs[index]
            val actualIndex = indexArgs[index].instantiateLevelParams(levelSubst)
            if (!expectedIndex.isDefEq(actualIndex, localCtx, localCtx)) {
                return null
            }
        }

        return applyRule(kRule, emptyList())
    }

    tryReduceKRule()?.let { return it }

    fun tryReduceCtorOrNatMajor(majorExpr: Expression): Expression? {
        val iotaMajorExpr = majorExpr.tryStringLitCtor() ?: majorExpr
        val [majorHead, majorArgs] = iotaMajorExpr.unfoldApp()

        val majorCtor = majorHead as? Expression.Const
        val constructorDecl = majorCtor?.decl as? Inductive.ConstructorVal
        if (majorCtor != null && constructorDecl != null) {
            val matchingRule = recursorDecl.rules.singleOrNull { rule ->
                rule.ctorName == majorCtor.name
            } ?: return null

            check(constructorDecl.numFields == matchingRule.nfields) {
                "Recursor rule for ${constructorDecl.name} has wrong nfields: expected ${constructorDecl.numFields}, got ${matchingRule.nfields}"
            }

            if (majorArgs.size != constructorDecl.numParams + matchingRule.nfields) return null
            val fieldArgs = majorArgs.drop(constructorDecl.numParams)
            return applyRule(matchingRule, fieldArgs)
        }

        return tryReduceNatValueRecursorMajor(recursorDecl, iotaMajorExpr, ::applyRule)
    }

    val majorWhnf = args[majorArgIndex].whnf(levelSubst, localCtx)
    tryReduceCtorOrNatMajor(majorWhnf)?.let { return it }

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

    return null
}

context(env: Environment)
private fun Expression.App.tryReduceRecursorHead(
    levelSubst: Map<Int, Level>,
    localCtx: List<Expression>,
    normalizedMajor: Expression? = null,
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

    fun tryReduceKRule(): Expression? {
        if (!recursorDecl.k) return null
        val kRule = recursorDecl.rules.singleOrNull() ?: return null
        if (kRule.nfields != 0) return null
        val kCtorDecl = env.constructorByName[kRule.ctorName] ?: return null
        if (kCtorDecl.numFields != 0 || kCtorDecl.numParams != recursorDecl.numParams) return null
        val indexArgs = args.drop(recursorArgsPrefixSize).take(recursorDecl.numIndices)
        if (indexArgs.size != recursorDecl.numIndices) return null

        var ctorTail: Expression = kCtorDecl.typeExpr.instantiateLevelParams(recursorLevelSubst)
        repeat(kCtorDecl.numParams + kCtorDecl.numFields) { binderIndex ->
            val ctorForall = ctorTail as? Expression.ForallE ?: return null
            val binderArg = if (binderIndex < kCtorDecl.numParams) {
                args[binderIndex].instantiateLevelParams(levelSubst)
            } else {
                return null
            }
            ctorTail = ctorForall.bodyExpr.applySubst(listOf(binderArg))
        }

        val [ctorResultHead, ctorResultArgs] = ctorTail.unfoldApp()
        val ctorResultConst = ctorResultHead as? Expression.Const ?: return null
        if (ctorResultConst.name != kCtorDecl.inductName) return null
        if (ctorResultArgs.size != recursorDecl.numParams + recursorDecl.numIndices) return null
        val expectedIndexArgs = ctorResultArgs.drop(recursorDecl.numParams)
        repeat(recursorDecl.numIndices) { index ->
            val expectedIndex = expectedIndexArgs[index]
            val actualIndex = indexArgs[index].instantiateLevelParams(levelSubst)
            if (!expectedIndex.isDefEq(actualIndex, localCtx, localCtx)) {
                return null
            }
        }

        return applyRule(kRule, emptyList())
    }

    tryReduceKRule()?.let { return it }

    val majorWhnf = normalizedMajor ?: args[majorArgIndex].whnf(levelSubst, localCtx)
    val iotaMajorWhnf = majorWhnf.tryStringLitCtor() ?: majorWhnf
    val [majorHead, majorArgs] = iotaMajorWhnf.unfoldApp()

    val majorCtor = majorHead as? Expression.Const
    val constructorDecl = majorCtor?.decl as? Inductive.ConstructorVal
    if (majorCtor != null && constructorDecl != null) {
        val matchingRule = recursorDecl.rules.singleOrNull { rule ->
            rule.ctorName == majorCtor.name
        } ?: return null

        check(constructorDecl.numFields == matchingRule.nfields) {
            "Recursor rule for ${constructorDecl.name} has wrong nfields: expected ${constructorDecl.numFields}, got ${matchingRule.nfields}"
        }

        if (majorArgs.size != constructorDecl.numParams + matchingRule.nfields) return null
        val fieldArgs = majorArgs.drop(constructorDecl.numParams)
        return applyRule(matchingRule, fieldArgs)
    }

    tryReduceNatValueRecursorMajor(recursorDecl, iotaMajorWhnf, ::applyRule)?.let { return it }

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

    return null
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
    normalizedMajor: Expression? = null,
): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val quotConst = headExpr as? Expression.Const ?: return null
    val quotDecl = quotConst.decl as? Declaration.Quot ?: return null
    if (quotDecl.kind != Declaration.Quot.Kind.Lift && quotDecl.kind != Declaration.Quot.Kind.Ind) return null
    val arity = quotDecl.typeExpr.forallBinderCount()
    if (args.size < arity) return null

    val majorWhnf = normalizedMajor ?: args[arity - 1].whnf(levelSubst, localCtx)
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
    fun tryDirection(
        value: Expression,
        constructorValue: Expression,
        valueCtx: List<Expression>,
        constructorCtx: List<Expression>,
    ): Boolean {
        val constructorSpine = constructorValue.unfoldApp()
        val constructorConst = constructorSpine.first as? Expression.Const ?: return false
        val constructor = constructorConst.decl as? Inductive.ConstructorVal ?: return false
        if (constructorSpine.second.size != constructor.numParams + constructor.numFields) return false
        val inductiveIndex = env.nameIndices[constructor.inductName] ?: return false
        val inductive = env.declarations[inductiveIndex] as? Inductive.InductiveVal ?: return false
        if (inductive.isRec || inductive.numIndices != 0 || inductive.ctors.size != 1) return false
        if (!value.inferType(localCtx = valueCtx).isDefEq(
                constructorValue.inferType(localCtx = constructorCtx),
                valueCtx,
                constructorCtx,
            )
        ) return false
        for (fieldIndex in 0 until constructor.numFields) {
            val projection = env.addCustomExpr {
                Expression.Proj(
                    typeName = inductiveIndex,
                    idx = fieldIndex,
                    struct = value.ie,
                    ie = it,
                )
            }
            val field = constructorSpine.second[constructor.numParams + fieldIndex]
            if (!projection.isDefEq(field, valueCtx, constructorCtx)) return false
        }
        return true
    }
    if (
        tryDirection(this, other, localCtxLeft, localCtxRight) ||
        tryDirection(other, this, localCtxRight, localCtxLeft)
    ) {
        return true
    }

    val leftType = this.inferType(localCtx = localCtxLeft).whnf(localCtx = localCtxLeft)
    val typeHead = leftType.asAppSpine().first as? Expression.Const ?: return false
    val typeIndex = env.nameIndices[typeHead.name] ?: return false
    val inductive = env.declarations[typeIndex] as? Inductive.InductiveVal ?: return false
    if (inductive.isRec || inductive.numIndices != 0 || inductive.ctors.size != 1) return false
    val constructor = env.declarations[inductive.ctors.single()] as? Inductive.ConstructorVal ?: return false
    if (constructor.numFields != 0) return false
    return leftType.isDefEq(other.inferType(localCtx = localCtxRight), localCtxLeft, localCtxRight)
}

context(env: Environment)
private fun Expression.tryProofIrrelevanceDefEqNoLog(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val tempLog = env.shouldLog
    env.shouldLog = false
    return try {
        this.tryProofIrrelevanceDefEq(other, localCtxLeft, localCtxRight)
    } finally {
        env.shouldLog = tempLog
    }
}

context(env: Environment)
private fun Expression.tryProofIrrelevanceDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val thisTy = this.inferType(localCtx = localCtxLeft)
    if (!thisTy.inferSort(localCtx = localCtxLeft).isLessOrEqual(Level.Zero)) return false
    return thisTy.isDefEq(other.inferType(localCtx = localCtxRight), localCtxLeft, localCtxRight)
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

    data class Frame(val expr: Expression, val visited: Boolean)

    val stack = ArrayDeque<Frame>()
    stack.add(Frame(this, false))
    while (stack.isNotEmpty()) {
        val (expr, visited) = stack.removeLast()
        if (env.maxLooseBVarIndexCache[expr.ie] != null) continue
        if (!visited) {
            stack.add(Frame(expr, true))
            when (expr) {
                is Expression.App -> {
                    stack.add(Frame(expr.fnExpr, false))
                    stack.add(Frame(expr.argExpr, false))
                }

                is Expression.ForallE -> {
                    stack.add(Frame(expr.typeExpr, false))
                    stack.add(Frame(expr.bodyExpr, false))
                }

                is Expression.Lam -> {
                    stack.add(Frame(expr.typeExpr, false))
                    stack.add(Frame(expr.bodyExpr, false))
                }

                is Expression.LetE -> {
                    stack.add(Frame(expr.typeExpr, false))
                    stack.add(Frame(expr.valueExpr, false))
                    stack.add(Frame(expr.bodyExpr, false))
                }

                is Expression.Mdata -> stack.add(Frame(expr.expr, false))
                is Expression.Proj -> stack.add(Frame(expr.structExpr, false))
                is Expression.Bvar,
                is Expression.Const,
                is Expression.NatVal,
                is Expression.Sort,
                is Expression.StrVal -> {
                }
            }
            continue
        }
        val value = when (expr) {
            is Expression.Bvar -> expr.bvar
            is Expression.App -> maxOf(
                env.maxLooseBVarIndexCache[expr.fnExpr.ie] ?: -1,
                env.maxLooseBVarIndexCache[expr.argExpr.ie] ?: -1,
            )

            is Expression.ForallE -> maxOf(
                env.maxLooseBVarIndexCache[expr.typeExpr.ie] ?: -1,
                (env.maxLooseBVarIndexCache[expr.bodyExpr.ie] ?: -1).descendBinder(),
            )

            is Expression.Lam -> maxOf(
                env.maxLooseBVarIndexCache[expr.typeExpr.ie] ?: -1,
                (env.maxLooseBVarIndexCache[expr.bodyExpr.ie] ?: -1).descendBinder(),
            )

            is Expression.LetE -> maxOf(
                env.maxLooseBVarIndexCache[expr.typeExpr.ie] ?: -1,
                env.maxLooseBVarIndexCache[expr.valueExpr.ie] ?: -1,
                (env.maxLooseBVarIndexCache[expr.bodyExpr.ie] ?: -1).descendBinder(),
            )

            is Expression.Mdata -> env.maxLooseBVarIndexCache[expr.expr.ie] ?: -1
            is Expression.Proj -> env.maxLooseBVarIndexCache[expr.structExpr.ie] ?: -1
            is Expression.Const, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> -1
        }
        env.maxLooseBVarIndexCache[expr.ie] = value
    }
    return env.maxLooseBVarIndexCache[this.ie] ?: -1
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
    data class Frame(val expr: Expression, val visited: Boolean)

    val cache = mutableMapOf<Int, Expression>()
    val stack = ArrayDeque<Frame>()
    stack.add(Frame(this, false))
    while (stack.isNotEmpty()) {
        val (expr, visited) = stack.removeLast()
        if (cache[expr.ie] != null) continue
        if (!visited) {
            stack.add(Frame(expr, true))
            when (expr) {
                is Expression.App -> {
                    stack.add(Frame(expr.fnExpr, false))
                    stack.add(Frame(expr.argExpr, false))
                }

                is Expression.ForallE -> {
                    stack.add(Frame(expr.typeExpr, false))
                    stack.add(Frame(expr.bodyExpr, false))
                }

                is Expression.Lam -> {
                    stack.add(Frame(expr.typeExpr, false))
                    stack.add(Frame(expr.bodyExpr, false))
                }

                is Expression.LetE -> {
                    stack.add(Frame(expr.typeExpr, false))
                    stack.add(Frame(expr.valueExpr, false))
                    stack.add(Frame(expr.bodyExpr, false))
                }

                is Expression.Mdata -> stack.add(Frame(expr.expr, false))
                is Expression.Proj -> stack.add(Frame(expr.structExpr, false))
                is Expression.Bvar,
                is Expression.Const,
                is Expression.NatVal,
                is Expression.Sort,
                is Expression.StrVal -> {
                }
            }
            continue
        }
        val result = when (expr) {
            is Expression.Bvar, is Expression.NatVal, is Expression.StrVal -> expr
            is Expression.Sort -> {
                val newLevel = expr.level.instantiateLevelParams(subst)
                if (newLevel == expr.level) expr else env.addCustomExpr { expr.copy(sort = newLevel.il, ie = it) }
            }

            is Expression.Const -> {
                val newUs = expr.levels.map { it.instantiateLevelParams(subst).il }
                val oldUs = expr.levels.map { it.il }
                if (newUs == oldUs) expr else env.addCustomExpr { expr.copy(us = newUs, ie = it) }
            }

            is Expression.App -> {
                val newFn = cache[expr.fnExpr.ie] ?: expr.fnExpr
                val newArg = cache[expr.argExpr.ie] ?: expr.argExpr
                if (newFn == expr.fnExpr && newArg == expr.argExpr) expr
                else env.addCustomExpr { expr.copy(fn = newFn.ie, arg = newArg.ie, ie = it) }
            }

            is Expression.ForallE -> {
                val newType = cache[expr.typeExpr.ie] ?: expr.typeExpr
                val newBody = cache[expr.bodyExpr.ie] ?: expr.bodyExpr
                if (newType == expr.typeExpr && newBody == expr.bodyExpr) expr
                else env.addCustomExpr { expr.copy(type = newType.ie, body = newBody.ie, ie = it) }
            }

            is Expression.Lam -> {
                val newType = cache[expr.typeExpr.ie] ?: expr.typeExpr
                val newBody = cache[expr.bodyExpr.ie] ?: expr.bodyExpr
                if (newType == expr.typeExpr && newBody == expr.bodyExpr) expr
                else env.addCustomExpr { expr.copy(type = newType.ie, body = newBody.ie, ie = it) }
            }

            is Expression.LetE -> {
                val newType = cache[expr.typeExpr.ie] ?: expr.typeExpr
                val newValue = cache[expr.valueExpr.ie] ?: expr.valueExpr
                val newBody = cache[expr.bodyExpr.ie] ?: expr.bodyExpr
                if (newType == expr.typeExpr && newValue == expr.valueExpr && newBody == expr.bodyExpr) expr
                else env.addCustomExpr { expr.copy(type = newType.ie, value = newValue.ie, body = newBody.ie, ie = it) }
            }

            is Expression.Mdata -> {
                val newExpr = cache[expr.expr.ie] ?: expr.expr
                if (newExpr == expr.expr) expr else env.addCustomExpr { expr.copy(_expr = newExpr.ie, ie = it) }
            }

            is Expression.Proj -> {
                val newStruct = cache[expr.structExpr.ie] ?: expr.structExpr
                if (newStruct == expr.structExpr) expr else env.addCustomExpr {
                    expr.copy(
                        struct = newStruct.ie,
                        ie = it
                    )
                }
            }
        }
        cache[expr.ie] = result
    }
    return cache[this.ie] ?: this
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
    fun cacheKey(expr: Expression, currentDepth: Int): Long =
        (currentDepth.toLong() shl 32) xor (expr.ie.toLong() and 0xffffffffL)

    data class Frame(val expr: Expression, val currentDepth: Int, val visited: Boolean)

    val stack = ArrayDeque<Frame>()
    stack.add(Frame(this, depth, false))
    while (stack.isNotEmpty()) {
        val (expr, currentDepth, visited) = stack.removeLast()
        val key = cacheKey(expr, currentDepth)
        if (cache[key] != null) continue
        if (expr.maxLooseBVarIndex() < currentDepth) {
            cache[key] = expr
            continue
        }
        if (!visited) {
            stack.add(Frame(expr, currentDepth, true))
            when (expr) {
                is Expression.App -> {
                    stack.add(Frame(expr.fnExpr, currentDepth, false))
                    stack.add(Frame(expr.argExpr, currentDepth, false))
                }

                is Expression.ForallE -> {
                    stack.add(Frame(expr.typeExpr, currentDepth, false))
                    stack.add(Frame(expr.bodyExpr, currentDepth + 1, false))
                }

                is Expression.Lam -> {
                    stack.add(Frame(expr.typeExpr, currentDepth, false))
                    stack.add(Frame(expr.bodyExpr, currentDepth + 1, false))
                }

                is Expression.LetE -> {
                    stack.add(Frame(expr.typeExpr, currentDepth, false))
                    stack.add(Frame(expr.valueExpr, currentDepth, false))
                    stack.add(Frame(expr.bodyExpr, currentDepth + 1, false))
                }

                is Expression.Mdata -> stack.add(Frame(expr.expr, currentDepth, false))
                is Expression.Proj -> stack.add(Frame(expr.structExpr, currentDepth, false))
                else -> {}
            }
            continue
        }
        val result = when (expr) {
            is Expression.Bvar -> rewriteBvar(expr, currentDepth)
            is Expression.App -> {
                val newFn = cache[cacheKey(expr.fnExpr, currentDepth)] ?: expr.fnExpr
                val newArg = cache[cacheKey(expr.argExpr, currentDepth)] ?: expr.argExpr
                if (newFn === expr.fnExpr && newArg === expr.argExpr) expr
                else env.addCustomExpr { expr.copy(fn = newFn.ie, arg = newArg.ie, ie = it) }
            }

            is Expression.ForallE -> {
                val newType = cache[cacheKey(expr.typeExpr, currentDepth)] ?: expr.typeExpr
                val newBody = cache[cacheKey(expr.bodyExpr, currentDepth + 1)] ?: expr.bodyExpr
                if (newType === expr.typeExpr && newBody === expr.bodyExpr) expr
                else env.addCustomExpr { expr.copy(type = newType.ie, body = newBody.ie, ie = it) }
            }

            is Expression.Lam -> {
                val newType = cache[cacheKey(expr.typeExpr, currentDepth)] ?: expr.typeExpr
                val newBody = cache[cacheKey(expr.bodyExpr, currentDepth + 1)] ?: expr.bodyExpr
                if (newType === expr.typeExpr && newBody === expr.bodyExpr) expr
                else env.addCustomExpr { expr.copy(type = newType.ie, body = newBody.ie, ie = it) }
            }

            is Expression.LetE -> {
                val newType = cache[cacheKey(expr.typeExpr, currentDepth)] ?: expr.typeExpr
                val newValue = cache[cacheKey(expr.valueExpr, currentDepth)] ?: expr.valueExpr
                val newBody = cache[cacheKey(expr.bodyExpr, currentDepth + 1)] ?: expr.bodyExpr
                if (newType === expr.typeExpr && newValue === expr.valueExpr && newBody === expr.bodyExpr) expr
                else env.addCustomExpr {
                    expr.copy(type = newType.ie, value = newValue.ie, body = newBody.ie, ie = it)
                }
            }

            is Expression.Mdata -> {
                val newExpr = cache[cacheKey(expr.expr, currentDepth)] ?: expr.expr
                if (newExpr === expr.expr) expr else env.addCustomExpr { expr.copy(_expr = newExpr.ie, ie = it) }
            }

            is Expression.Proj -> {
                val newStruct = cache[cacheKey(expr.structExpr, currentDepth)] ?: expr.structExpr
                if (newStruct === expr.structExpr) expr else env.addCustomExpr {
                    expr.copy(
                        struct = newStruct.ie,
                        ie = it
                    )
                }
            }

            else -> expr
        }
        cache[key] = result
    }
    return cache[cacheKey(this, depth)] ?: this
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