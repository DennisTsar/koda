package io.github.opletter.koda

private var debugClosedEvaluation = false
private var debugTargetDeclaration = false
private const val debugTargetIndex = -1//21_000_000///51_500_000
private const val semanticStepLimit = 1_000_000

internal data class StructureEtaRecursorInfo(
    val inductiveDeclIndex: Int,
    val inductiveDecl: Inductive.InductiveVal,
    val constructorDecl: Inductive.ConstructorVal,
    val rule: Inductive.RecursorVal.RecursorRule,
)

internal data class ClosedEvalCacheKey(
    val expressionId: Int,
    val unfoldDefinitionsAtRoot: Boolean,
)

internal class SemanticRuntime {
    internal val instantiatedRecursorRules: MutableMap<ClosedRecursorRuleKey, Expression> = mutableMapOf()
    internal val looseBvarIndices: MutableMap<Int, List<Int>> = mutableMapOf()
    internal val closedValues: MutableMap<ClosedEvalCacheKey, ClosedValue> = mutableMapOf()
    internal val localEnvironments: MutableMap<Int, ClosedEvalEnv> = mutableMapOf()
    internal val rootEnvironments: MutableMap<Int, ClosedEvalEnv.Root> = mutableMapOf()
    internal val inferredTypes: MutableMap<InferTypeCacheKey, ClosedClosure> = mutableMapOf()
    internal val proofArgumentMasks: MutableMap<Long, BooleanArray?> = mutableMapOf()
    internal var activeConversions: Int = 0
    internal var remainingSteps: Int = 0

    fun clear() {
        instantiatedRecursorRules.clear()
        looseBvarIndices.clear()
        closedValues.clear()
        localEnvironments.clear()
        rootEnvironments.clear()
        inferredTypes.clear()
        proofArgumentMasks.clear()
        activeConversions = 0
        remainingSteps = 0
    }
}

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
        debugTargetDeclaration = index == debugTargetIndex && data is Declaration
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
        if (index < debugTargetIndex) {
            when (data) {
                is Name -> data.registerInto(env)
                is Level -> data.registerInto(env)
                is Expression -> data.registerInto(env)
                is Declaration -> {
                    data.registerInto(env)
                    env.declTypeByName[data.name] = data.typeExpr
                    env.counter++
                }

                is Inductive -> {
                    data.registerInto(env)
                    (data.types + data.ctors + data.recs).forEach { declaration ->
                        env.declTypeByName[declaration.name] = declaration.typeExpr
                    }
                }

                is Meta -> {}
            }
            return@forEachIndexed
        }
//        val shouldTimeDeclaration = data is Declaration && debugTimingRanges.any { index in it }
//        debugTargetDeclaration = index == debugTargetIndex && data is Declaration
//        if (debugTargetDeclaration && data is Declaration) {
//            debugDeclarationShape(data)
//        }
        val itemStart = env.clock.elapsedNow()
//        if (env.shouldLog || shouldTimeDeclaration) {
//            println("started: ${env.clock.elapsedNow()}")
//            val dataName = (data as? NamedDecl)?.name?.toStringDetailed() ?: data::class.simpleName
//            println("i: index=$index")
//            println("$dataName $data")
//            println("---")
//        }
        when (data) {
            is Name -> {
                data.registerInto(env)
            }

            is Level -> {
//                println(env.levels.values.toList())
//                println(data)
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
                val debugStart = env.clock.elapsedNow()
                try {
                    val declaredTypeSortLevel = data.typeExpr.inferSort()
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
                } catch (error: Throwable) {
                    println(
                        "error while checking declaration: name=${data.name.toStringDetailed()} " +
                                "index=$index defEqCalls=${env.defEqCalls} inferCache=${env.inferTypeCacheNoLevelSubst.size} " +
                                "whnfCache=${env.whnfCacheNoLevelSubst.size + env.whnfCacheWithCtxNoLevelSubst.size}"
                    )
                    throw error
                }
//                if (shouldTimeDeclaration) {
//                    println("i: checked declaration at index=$index start=$debugStart end=${env.clock.elapsedNow()}")
//                }

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
                        "defEqCacheSize=${env.defEqCache.size}"
            )
        }
        if (data is Declaration || data is Inductive) {
            env.clearCustom()
            if (data is Declaration) {
                val declarationElapsed = env.clock.elapsedNow() - itemStart
                if (declarationElapsed.inWholeMilliseconds >= 1_000) {
                    val declarationStats = if (data is Declaration) """
                        defEqCalls=${env.defEqCalls} defEqCache=${env.defEqCache.size}
                        inferCache=${env.inferTypeCacheNoLevelSubst.size}
                        whnfCache=${env.whnfCacheNoLevelSubst.size + env.whnfCacheWithCtxNoLevelSubst.size}
                        proofIrrelevance=${env.proofIrrelevanceSuccesses}/${env.proofIrrelevanceAttempts}
                        typedProofSkips=${env.typedCongruenceProofSkips}
                    """.trimIndent().replace('\n', ' ') else null
                    println(
                        "slow declaration: name=${data.name.toStringDetailed()} index=$index " +
                                "elapsed=$declarationElapsed ${checkNotNull(declarationStats)}"
                    )
                }
            }
        }
//        if (env.shouldLog) {
//            println("ended: ${env.clock.elapsedNow()}")
//        }
//        println("apple: ${env.levels.size} // ${env.expressions.size} // ${env.declarations.size} // ${env.names.size}")
    }
}


context(env: Environment)
private fun Expression.rigidTypeIsProp(): Boolean {
    val [head, arguments] = asAppSpine()
    if (head !is Expression.Const) return false
    var type = head.inferType(validate = false)
    var localCtx = emptyList<Expression>()
    repeat(arguments.size) {
        val forall = type.whnf(localCtx = localCtx) as? Expression.ForallE ?: return false
        localCtx = env.consLocalCtx(forall.typeExpr, localCtx)
        type = forall.bodyExpr
    }
    val sort = type.whnf(localCtx = localCtx) as? Expression.Sort ?: return false
    return sort.level.isLessOrEqual(Level.Zero)
}

context(env: Environment)
private fun Expression.rigidProofStatus(): Boolean? {
    val [head, arguments] = asAppSpine()
    if (head !is Expression.Const) return null
    var type = head.inferType(validate = false)
    var localCtx = emptyList<Expression>()
    repeat(arguments.size) {
        val forall = type.whnf(localCtx = localCtx) as? Expression.ForallE ?: return null
        localCtx = env.consLocalCtx(forall.typeExpr, localCtx)
        type = forall.bodyExpr
    }
    return type.inferSort(localCtx = localCtx, validate = false).isLessOrEqual(Level.Zero)
}

context(env: Environment)
fun typeCheckDeclaration(value: Expression, expectedType: Expression): Boolean {
    if (env.shouldLog) println("found value: ${value/*.toStringDetailed()*/}")
    return value.checkHasType(expectedType)
}

context(env: Environment)
private fun Expression.checkHasType(
    expectedType: Expression,
    initialLocalCtx: List<Expression> = emptyList(),
): Boolean = checkHasType(
    ClosedClosure(expectedType, initialLocalCtx.closedEvalEnv()),
    initialLocalCtx,
)

context(env: Environment)
private fun Expression.checkHasType(
    expectedType: ClosedClosure,
    initialLocalCtx: List<Expression>,
): Boolean {
    val plan = openLambdasAgainst(expectedType, initialLocalCtx)
    if (!plan.valid) return false
    return plan.body.matchesExpectedType(plan.expectedType, plan.localCtx)
}

private data class LambdaCheckPlan(
    val body: Expression,
    val expectedType: ClosedClosure,
    val localCtx: List<Expression>,
    val opened: Boolean,
    val valid: Boolean,
)

context(env: Environment)
private fun Expression.openLambdasAgainst(
    initialExpectedType: ClosedClosure,
    initialLocalCtx: List<Expression>,
): LambdaCheckPlan {
    var value = this
    var expected = initialExpectedType
    var localCtx = initialLocalCtx
    var opened = false
    while (true) {
        if (value is Expression.Mdata) {
            value = value.expr
            continue
        }
        val lambda = value as? Expression.Lam ?: break
        opened = true
        val baseLocals = localCtx.closedEvalEnv()
        val functionType = expected.inferFunctionType(baseLocals, localCtx, lambda)
        val pi = functionType.head.expression as Expression.ForallE
        val expectedDomain = ClosedClosure(pi.typeExpr, functionType.head.locals)
        requireSort(lambda.typeExpr.inferType(localCtx = localCtx), lambda.typeExpr, localCtx)
        val actualDomain = ClosedClosure(lambda.typeExpr, baseLocals)
        val domainMatchesSemantically = expectedDomain.trySemanticDefEq(actualDomain)
        if (
            !domainMatchesSemantically &&
            !expectedDomain.reify(baseLocals).isDefEqWithoutSemantic(
                lambda.typeExpr,
                localCtx,
                localCtx,
            )
        ) return LambdaCheckPlan(value, expected, localCtx, opened, false)
        val neutral = ClosedClosure(
            Expression.Bvar(-localCtx.size - 1, Int.MIN_VALUE),
            ClosedEvalEnv.Empty,
        ).also { it.semanticType = expectedDomain }
        expected = ClosedClosure(
            pi.bodyExpr,
            ClosedEvalEnv.Bind(neutral, functionType.head.locals),
        )
        localCtx = env.consLocalCtx(lambda.typeExpr, localCtx)
        value = lambda.bodyExpr
    }
    return LambdaCheckPlan(value, expected, localCtx, opened, true)
}

context(env: Environment)
private fun Expression.matchesExpectedType(
    expected: ClosedClosure,
    localCtx: List<Expression>,
): Boolean = inferTypeCore(localCtx = localCtx).matchesExpectedType(expected, localCtx)

context(env: Environment)
private fun InferredTypeResult.matchesExpectedType(
    expected: ClosedClosure,
    localCtx: List<Expression>,
): Boolean {
    val baseLocals = localCtx.closedEvalEnv()
    if (env.shouldLog) println("expected type detailed: ${expected.reify(baseLocals).toStringDetailed()}")
    return when (this) {
        is InferredTypeResult.Syntax -> {
            if (env.shouldLog) println("inferred type of value: $expression")
            if (env.shouldLog) println("inferred type detailed: ${expression.toStringDetailed()}")
            val semanticMatch = expected.trySemanticDefEq(ClosedClosure(expression, baseLocals))
            if (semanticMatch) true else {
                val expectedSyntax = expected.reify(baseLocals)
                expectedSyntax.isDefEqWithoutSemantic(expression, localCtx, localCtx)
            }
        }

        is InferredTypeResult.Semantic -> {
            if (env.shouldLog) {
                val inferredExpression = closure.reify(baseLocals)
                println("inferred type of value: $inferredExpression")
                println("inferred type detailed: ${inferredExpression.toStringDetailed()}")
            }
            val semanticMatch = expected.trySemanticDefEq(closure)
            if (semanticMatch) {
                true
            } else {
                val expectedSyntax = expected.reify(baseLocals)
                val inferredSyntax = closure.reify(baseLocals)
                expectedSyntax.isDefEqWithoutSemantic(inferredSyntax, localCtx, localCtx)
            }
        }
    }
}

context(env: Environment)
private fun Expression.isDefEqWithoutSemantic(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    env.semanticRuntime.activeConversions += 1
    return try {
        isDefEq(other, localCtxLeft, localCtxRight)
    } finally {
        env.semanticRuntime.activeConversions -= 1
    }
}

context(env: Environment)
fun Expression.isDefEq(
    other: Expression,
    localCtxLeft: List<Expression> = emptyList(),
    localCtxRight: List<Expression> = emptyList(),
): Boolean {
    env.defEqCalls += 1
//    val traceDefEq = false
//    if (traceDefEq) println("debug defeq phase: start")
    if (this === other) return true
    val cacheKey = this.defEqCacheKey(other, localCtxLeft, localCtxRight)
    if (env.defEqEquivalences.areEquivalent(cacheKey)) return true
    env.defEqCache[cacheKey]?.let { cached ->
        env.defEqCacheHits += 1
        return cached
    }
    fun finish(value: Boolean): Boolean {
        env.defEqCache[cacheKey] = value
        if (value) env.defEqEquivalences.addEquivalent(cacheKey)
        return value
    }

//    if (traceDefEq) println("debug defeq phase: quick")
    this.quickIsDefEq(other, localCtxLeft, localCtxRight)?.let { return finish(it) }
    if (
        (this.asNatLiteralValue() != null || other.asNatLiteralValue() != null) &&
        this.tryNatLiteralDefEq(other, localCtxLeft, localCtxRight)
    ) {
        return finish(true)
    }
//    if (traceDefEq) println("debug defeq phase: bool")
    this.tryClosedBoolTrueDefEq(other, localCtxLeft)?.let { return finish(it) }
    other.tryClosedBoolTrueDefEq(this, localCtxRight)?.let { return finish(it) }
//    if (traceDefEq) println("debug defeq phase: structural")
    this.tryStructuralDefEq(other)?.let { return finish(it) }
    if (this.tryKnownDefEqCongruence(other, localCtxLeft, localCtxRight)) return finish(true)

//    if (traceDefEq) println("debug defeq phase: cheap whnf")
    val leftCore = this.whnfCore(localCtxLeft, cheapProjection = true)
    val rightCore = other.whnfCore(localCtxRight, cheapProjection = true)
//    if (traceDefEq) println("debug defeq phase: core quick")
    leftCore.quickIsDefEq(rightCore, localCtxLeft, localCtxRight)?.let { return finish(it) }
    leftCore.tryStructuralDefEq(rightCore)?.let { return finish(it) }
    if (leftCore.tryKnownDefEqCongruence(rightCore, localCtxLeft, localCtxRight)) return finish(true)
    if (leftCore.tryProofIrrelevanceDefEqNoLog(rightCore, localCtxLeft, localCtxRight)) {
        return finish(true)
    }
    if (leftCore.trySemanticDefEq(rightCore, localCtxLeft, localCtxRight)) {
        return finish(true)
    }
//    if (traceDefEq) println("debug defeq phase: lazy delta")
    val lazyResult = leftCore.lazyDeltaDefEq(rightCore, localCtxLeft, localCtxRight)
//    if (traceDefEq) {
//        println("debug defeq phase: after lazy delta")
//        println("debug lazy left=${lazyResult.left.debugShallow()}")
//        println("debug lazy right=${lazyResult.right.debugShallow()}")
//    }
    lazyResult.decision?.let { return finish(it) }

    val leftProjection = lazyResult.left as? Expression.Proj
    val rightProjection = lazyResult.right as? Expression.Proj
    if (
        leftProjection != null && rightProjection != null &&
        leftProjection.projIndex == rightProjection.projIndex &&
        !leftProjection.structuresHaveSameConstantHead(rightProjection, localCtxLeft, localCtxRight) &&
        leftProjection.lazyProjectionDefEq(rightProjection, localCtxLeft, localCtxRight)
    ) {
        return finish(true)
    }

//    if (traceDefEq) println("debug defeq phase: full whnf")
    val leftWhnf = lazyResult.left.whnfCore(localCtxLeft, cheapProjection = false)
    val rightWhnf = lazyResult.right.whnfCore(localCtxRight, cheapProjection = false)
//    if (traceDefEq) {
//        println("debug full left=${leftWhnf.debugShallow()}")
//        println("debug full right=${rightWhnf.debugShallow()}")
//    }
    if (leftWhnf !== lazyResult.left || rightWhnf !== lazyResult.right) {
        return finish(
            leftWhnf.isDefEq(rightWhnf, localCtxLeft, localCtxRight)
        )
    }

//    if (traceDefEq) println("debug defeq phase: congruence")
    val result = leftWhnf.isDefEqWhnf(rightWhnf, localCtxLeft, localCtxRight)
//    if (traceDefEq) println("debug defeq phase: done=$result")
    return finish(result)
}

context(env: Environment)
private fun List<Expression>.closedEvalEnv(): ClosedEvalEnv {
    if (isEmpty()) return ClosedEvalEnv.Empty
    if (!env.localCtxHasValues(this)) {
        return env.semanticRuntime.rootEnvironments.getOrPut(env.localCtxId(this)) {
            ClosedEvalEnv.Root(this)
        }
    }
    return env.semanticRuntime.localEnvironments.getOrPut(env.localCtxId(this)) {
        var locals: ClosedEvalEnv = ClosedEvalEnv.Empty
        for (index in indices.reversed()) {
            val value = env.localCtxValue(this, index)
            val bindingType = ClosedClosure(this[index], locals)
            val closure = (if (value == null) {
                ClosedClosure(Expression.Bvar(index - size, Int.MIN_VALUE), ClosedEvalEnv.Empty)
            } else {
                ClosedClosure(value, locals)
            }).also { it.semanticType = bindingType }
            locals = ClosedEvalEnv.Bind(closure, locals)
        }
        locals
    }
}

context(env: Environment)
private fun Expression.trySemanticDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    if (env.semanticRuntime.activeConversions != 0) return false
    env.semanticRuntime.activeConversions += 1
    env.semanticRuntime.remainingSteps = semanticStepLimit
    return try {
        ClosedClosure(this, localCtxLeft.closedEvalEnv()).closedDefEq(
            ClosedClosure(other, localCtxRight.closedEvalEnv()),
            nextNeutral = -maxOf(localCtxLeft.size, localCtxRight.size) - 1,
        )
    } finally {
        env.semanticRuntime.remainingSteps = 0
        env.semanticRuntime.activeConversions -= 1
    }
}

context(env: Environment)
private fun ClosedClosure.trySemanticWhnf(): ClosedValue? {
    if (env.semanticRuntime.activeConversions != 0) return null
    env.semanticRuntime.activeConversions += 1
    env.semanticRuntime.remainingSteps = semanticStepLimit
    return try {
        closedWhnf()
    } finally {
        env.semanticRuntime.remainingSteps = 0
        env.semanticRuntime.activeConversions -= 1
    }
}

context(env: Environment)
private fun ClosedClosure.trySemanticDefEq(other: ClosedClosure): Boolean {
    if (
        expression === other.expression &&
        pendingArguments.size == other.pendingArguments.size &&
        pendingArguments.indices.all { pendingArguments[it] === other.pendingArguments[it] } &&
        (locals === other.locals || expression.maxLooseBVarIndex() < 0)
    ) {
        return true
    }
    if (env.semanticRuntime.activeConversions != 0) return false
    env.semanticRuntime.activeConversions += 1
    env.semanticRuntime.remainingSteps = semanticStepLimit
    return try {
        closedDefEq(
            other,
            nextNeutral = -maxOf(locals.semanticDepth(), other.locals.semanticDepth()) - 1,
            trace = debugTargetDeclaration,
        )
    } finally {
        env.semanticRuntime.remainingSteps = 0
        env.semanticRuntime.activeConversions -= 1
    }
}

private fun ClosedEvalEnv.semanticDepth(): Int {
    var depth = 0
    var current = this
    while (current is ClosedEvalEnv.Bind) {
        depth += 1
        current = current.tail
    }
    if (current is ClosedEvalEnv.Root) depth += current.depth
    return depth
}

context(env: Environment)
private fun ClosedEvalEnv.Root.localIsProof(index: Int): Boolean {
    if (index !in localCtx.indices) return false
    when (proofStatus[index].toInt()) {
        1 -> return false
        2 -> return true
    }
    proofStatus[index] = 1
    val binderType = localCtx[index].lift(index + 1)
    val isProof = binderType
        .inferSort(localCtx = localCtx, validate = false)
        .isLessOrEqual(Level.Zero)
    proofStatus[index] = if (isProof) 2 else 1
    return isProof
}

context(env: Environment)
private fun ClosedClosure.reify(baseLocals: ClosedEvalEnv): Expression {
    val reified = mutableMapOf<ClosedClosure, Expression>()
    fun reifyClosure(closure: ClosedClosure): Expression {
        reified[closure]?.let { return it }
        var currentLocals = closure.locals
        val requiredBindings = when (val expression = closure.expression) {
            is Expression.Bvar -> if (expression.ie == Int.MIN_VALUE) 0
            else expression.maxLooseBVarIndex() + 1

            is Expression.NatVal -> if (expression.ie == Int.MIN_VALUE) 0
            else expression.maxLooseBVarIndex() + 1

            else -> expression.maxLooseBVarIndex() + 1
        }
        val substitutions = ArrayList<Expression>(requiredBindings)
        while (
            substitutions.size < requiredBindings &&
            currentLocals is ClosedEvalEnv.Bind &&
            currentLocals !== baseLocals
        ) {
            substitutions += reifyClosure(currentLocals.value)
            currentLocals = currentLocals.tail
        }
        if (
            substitutions.size < requiredBindings &&
            currentLocals is ClosedEvalEnv.Root &&
            currentLocals !== baseLocals
        ) {
            val targetDepth = baseLocals.semanticDepth()
            val sourceDepth = currentLocals.depth
            repeat(minOf(requiredBindings - substitutions.size, sourceDepth)) { index ->
                substitutions += env.addCustomExpr {
                    Expression.Bvar(targetDepth - sourceDepth + index, it)
                }
            }
        }
        var result = closure.expression.applySubst(substitutions)
        if (result.ie == Int.MIN_VALUE) {
            result = when (val transient = result) {
                is Expression.Bvar -> env.addCustomExpr {
                    transient.copy(
                        bvar = transient.bvar + baseLocals.semanticDepth(),
                        ie = it,
                    )
                }

                is Expression.NatVal -> env.addCustomExpr { transient.copy(ie = it) }
                else -> error("Unexpected transient semantic expression: ${transient::class.simpleName}")
            }
        }
        val arguments = closure.cachedArguments ?: closure.pendingArguments
        if (arguments.isNotEmpty()) {
            result = result.applyArgs(arguments.map(::reifyClosure))
        }
        reified[closure] = result
        return result
    }
    return reifyClosure(this)
}

context(env: Environment)
private fun ClosedClosure.inferFunctionType(
    baseLocals: ClosedEvalEnv,
    localCtx: List<Expression>,
    subject: Expression,
): ClosedValue {
    val semantic = trySemanticWhnf()
    if (semantic != null && semantic.arguments.isEmpty() && semantic.head.expression is Expression.ForallE) {
        return semantic
    }
    val syntax = reify(baseLocals).whnf(localCtx = localCtx)
    val forall = syntax as? Expression.ForallE
        ?: error("Expected function type for app ${subject.toStringDetailed()}, got ${syntax.toStringDetailed()}")
    return ClosedValue(forall, baseLocals, false, ClosedArgs.Empty)
}

context(env: Environment)
private fun Expression.tryClosedBoolTrueDefEq(other: Expression, localCtx: List<Expression>): Boolean? {
    if (!other.isBoolTrueConst() || this.maxLooseBVarIndex() >= 0 && !env.eagerReduction) return null
    val start = env.clock.elapsedNow()
    return this.closedBoolValue(localCtx).also { result ->
//        if (debugClosedEvaluation || debugTargetDeclaration) {
//            println("closed Bool evaluation: expr=${this.ie} result=$result elapsed=${env.clock.elapsedNow() - start}")
//        }
    }
}

context(env: Environment)
private fun Expression.isBoolFalseConst(): Boolean {
    val constant = this as? Expression.Const ?: return false
    val falseName = constant.name as? Name.Str ?: return false
    if (falseName.str != "false") return false
    val boolName = env.names[falseName.pre] as? Name.Str ?: return false
    return boolName.pre == 0 && boolName.str == "Bool"
}

context(env: Environment)
private fun Expression.isBoolTrueConst(): Boolean {
    val constant = this as? Expression.Const ?: return false
    val trueName = constant.name as? Name.Str ?: return false
    if (trueName.str != "true") return false
    val boolName = env.names[trueName.pre] as? Name.Str ?: return false
    return boolName.pre == 0 && boolName.str == "Bool"
}

internal sealed interface ClosedEvalEnv {
    data object Empty : ClosedEvalEnv
    class Root(val localCtx: List<Expression>) : ClosedEvalEnv {
        val depth: Int get() = localCtx.size
        val proofStatus = ByteArray(depth)
    }
    class Bind(val value: ClosedClosure, val tail: ClosedEvalEnv) : ClosedEvalEnv
}

internal sealed class ClosedArgs(
    val size: Int,
) : Iterable<ClosedClosure> {
    abstract operator fun get(index: Int): ClosedClosure

    val indices: IntRange get() = 0 until size

    fun isEmpty(): Boolean = size == 0

    fun isNotEmpty(): Boolean = size != 0

    fun getOrNull(index: Int): ClosedClosure? =
        if (index in indices) get(index) else null

    override fun iterator(): Iterator<ClosedClosure> = object : Iterator<ClosedClosure> {
        private var index = 0

        override fun hasNext(): Boolean = index < size

        override fun next(): ClosedClosure {
            if (!hasNext()) throw NoSuchElementException()
            return get(index++)
        }
    }

    data object Empty : ClosedArgs(0) {
        override fun get(index: Int): ClosedClosure = throw IndexOutOfBoundsException(index.toString())
    }

    private class One(val value: ClosedClosure) : ClosedArgs(1) {
        override fun get(index: Int): ClosedClosure =
            if (index == 0) value else throw IndexOutOfBoundsException(index.toString())
    }

    private class Cons(
        val value: ClosedClosure,
        val tail: ClosedArgs,
    ) : ClosedArgs(tail.size + 1) {
        override fun get(index: Int): ClosedClosure {
            checkElementIndex(index, size)
            if (index == 0) return value
            return getAt(tail, index - 1)
        }
    }

    private class Snoc(
        val init: ClosedArgs,
        val value: ClosedClosure,
    ) : ClosedArgs(init.size + 1) {
        override fun get(index: Int): ClosedClosure {
            checkElementIndex(index, size)
            if (index == init.size) return value
            return getAt(init, index)
        }
    }

    private class Node(
        val left: ClosedArgs,
        val right: ClosedArgs,
    ) : ClosedArgs(left.size + right.size) {
        override fun get(index: Int): ClosedClosure {
            checkElementIndex(index, size)
            return getAt(this, index)
        }
    }

    private class Slice(
        val base: ClosedArgs,
        val offset: Int,
        size: Int,
    ) : ClosedArgs(size) {
        override fun get(index: Int): ClosedClosure {
            checkElementIndex(index, size)
            return getAt(base, offset + index)
        }
    }

    fun prepend(value: ClosedClosure): ClosedArgs = Cons(value, this)

    fun append(value: ClosedClosure): ClosedArgs = Snoc(this, value)

    fun concat(other: ClosedArgs): ClosedArgs = concat(this, other)

    fun takeArgs(count: Int): ClosedArgs {
        require(count in 0..size)
        if (count == 0) return Empty
        if (count == size) return this
        return when (this) {
            is Slice -> Slice(base, offset, count)
            else -> Slice(this, 0, count)
        }
    }

    fun dropArgs(count: Int): ClosedArgs {
        require(count in 0..size)
        if (count == 0) return this
        if (count == size) return Empty
        var current = this
        var remaining = count
        while (remaining > 0 && current is Cons) {
            current = current.tail
            remaining -= 1
        }
        if (remaining == 0) return current
        return when (this) {
            is Slice -> Slice(base, offset + count, size - count)
            else -> Slice(this, count, size - count)
        }
    }

    companion object {
        fun fromList(values: List<ClosedClosure>): ClosedArgs {
            fun build(from: Int, until: Int): ClosedArgs {
                if (from == until) return Empty
                if (from + 1 == until) return One(values[from])
                val middle = (from + until) ushr 1
                return Node(build(from, middle), build(middle, until))
            }
            return build(0, values.size)
        }

        private fun concat(left: ClosedArgs, right: ClosedArgs): ClosedArgs {
            if (left === Empty) return right
            if (right === Empty) return left
            return Node(left, right)
        }

        private fun getAt(root: ClosedArgs, index: Int): ClosedClosure {
            var current = root
            var remaining = index
            while (true) {
                when (current) {
                    is Cons -> {
                        if (remaining == 0) return current.value
                        remaining -= 1
                        current = current.tail
                    }

                    is Snoc -> {
                        if (remaining == current.init.size) return current.value
                        current = current.init
                    }

                    is Node -> {
                        if (remaining < current.left.size) {
                            current = current.left
                        } else {
                            remaining -= current.left.size
                            current = current.right
                        }
                    }

                    is Slice -> {
                        remaining += current.offset
                        current = current.base
                    }

                    is One -> return current.value
                    Empty -> throw IndexOutOfBoundsException(index.toString())
                }
            }
        }

        private fun checkElementIndex(index: Int, size: Int) {
            if (index !in 0 until size) throw IndexOutOfBoundsException("index=$index size=$size")
        }
    }
}

internal open class ClosedClosure(
    var expression: Expression,
    var locals: ClosedEvalEnv,
    var isProof: Boolean = false,
    val pendingArguments: ClosedArgs = ClosedArgs.Empty,
) {
    var cachedArguments: ClosedArgs? = null
    var cachedValue: ClosedValue? = null
    var semanticType: ClosedClosure? = null
}

private fun ClosedClosure.withSemanticType(type: ClosedClosure): ClosedClosure {
    if (semanticType == null) semanticType = type
    return this
}

internal class ClosedValue(
    expression: Expression,
    locals: ClosedEvalEnv,
    isProof: Boolean,
    val arguments: ClosedArgs,
    semanticType: ClosedClosure? = null,
    val projection: ClosedProjection? = null,
) : ClosedClosure(expression, locals, isProof, pendingArguments = arguments) {
    val head: ClosedClosure get() = this

    init {
        this.semanticType = semanticType
    }
}

internal class ClosedProjection(
    val descriptor: Expression.Proj,
    val structure: ClosedValue,
)

private fun ClosedValue.asClosure(arguments: ClosedArgs = this.arguments): ClosedClosure {
    if (projection == null) {
        return ClosedClosure(
            head.expression,
            head.locals,
            head.isProof,
            pendingArguments = arguments,
        ).also { it.semanticType = head.semanticType }
    }
    return ClosedClosure(
        head.expression,
        head.locals,
        head.isProof,
    ).also {
        it.semanticType = head.semanticType
        it.cachedValue = if (arguments === this.arguments) this else {
            ClosedValue(
                head.expression,
                head.locals,
                head.isProof,
                arguments,
                head.semanticType,
                projection,
            )
        }
    }
}

private data class ClosedLocalLookup(
    val closure: ClosedClosure?,
    val neutralIndex: Int,
    val isProof: Boolean = false,
    val semanticType: ClosedClosure? = null,
)

private data class ClosedDefEqTask(
    val left: ClosedClosure,
    val right: ClosedClosure,
    val nextNeutral: Int,
    val sameTypeKnown: Boolean,
    val expectedType: ClosedExpectedType? = null,
    val fallback: ClosedDefEqFallback? = null,
)

private class ClosedDefEqFallback(
    val alternative: ClosedDefEqTask,
    val outer: ClosedDefEqFallback?,
)

private sealed interface ClosedExpectedType {
    data class Closure(val value: ClosedClosure) : ClosedExpectedType

    data class ConstantArgument(
        val head: Expression.Const,
        val arguments: ClosedArgs,
        val index: Int,
        val isProof: Boolean? = null,
    ) : ClosedExpectedType
}

private data class ClosedDefEqState(
    val leftExpressionId: Int,
    val leftLocals: ClosedEvalEnv,
    val leftArguments: ClosedArgs,
    val rightExpressionId: Int,
    val rightLocals: ClosedEvalEnv,
    val rightArguments: ClosedArgs,
    val leftCachedValue: ClosedValue?,
    val rightCachedValue: ClosedValue?,
    val nextNeutral: Int,
    val sameTypeKnown: Boolean,
    val fallback: ClosedDefEqFallback?,
)

internal data class ClosedRecursorRuleKey(
    val recursorName: Name,
    val levelIds: List<Int>,
    val ruleExprId: Int,
)

private enum class ClosedNatPrimitive(val arity: Int) {
    Succ(1), Add(2), Sub(2), Mul(2), Pow(2), Div(2), Mod(2), Beq(2), Ble(2)
}

private sealed interface ClosedEvalContinuation {
    data class Force(
        val closure: ClosedClosure,
        val outerArgs: ClosedArgs,
    ) : ClosedEvalContinuation

    data class Projection(
        val projection: Expression.Proj,
        val locals: ClosedEvalEnv,
        val outerArgs: ClosedArgs,
        val unfoldDefinitions: Boolean,
        val semanticType: ClosedClosure?,
    ) : ClosedEvalContinuation

    data class Quotient(
        val quotConst: Expression.Const,
        val quotient: Declaration.Quot,
        val arguments: ClosedArgs,
        val arity: Int,
        val unfoldDefinitions: Boolean,
    ) : ClosedEvalContinuation

    data class Recursor(
        val recursorConst: Expression.Const,
        val recursor: Inductive.RecursorVal,
        val recursorArgs: ClosedArgs,
        val unfoldDefinitions: Boolean,
    ) : ClosedEvalContinuation

    data class NatOperand(
        val primitiveConst: Expression.Const,
        val primitive: ClosedNatPrimitive,
        val operands: ClosedArgs,
        val extraArgs: ClosedArgs,
        val values: List<NatValue>,
        val operandIndex: Int,
    ) : ClosedEvalContinuation
}

context(env: Environment)
private fun Expression.closedBoolValue(localCtx: List<Expression> = emptyList()): Boolean? {
    val value = ClosedClosure(this, localCtx.closedEvalEnv()).closedWhnf(trace = debugTargetDeclaration) ?: return null
    if (value.arguments.isNotEmpty()) return null
    return when {
        value.head.expression.isBoolTrueConst() -> true
        value.head.expression.isBoolFalseConst() -> false
        else -> null
    }
}

context(env: Environment)
private fun ClosedClosure.closedDefEq(
    other: ClosedClosure,
    nextNeutral: Int = -1,
    trace: Boolean = false,
    expectedType: ClosedExpectedType? = null,
): Boolean {
    val pending = ArrayDeque<ClosedDefEqTask>()
    val visited = mutableSetOf<ClosedDefEqState>()
    val instantiatedRecursorRules = env.semanticRuntime.instantiatedRecursorRules
    val looseBvarIndices = env.semanticRuntime.looseBvarIndices
    val resolvedExpectedTypes = mutableMapOf<ClosedExpectedType, ClosedClosure?>()
    val expectedTypePropCache = mutableMapOf<ClosedExpectedType, Boolean>()

    fun bindingAt(locals: ClosedEvalEnv, index: Int): ClosedLocalLookup {
        var current = locals
        var remaining = index
        while (current is ClosedEvalEnv.Bind) {
            if (remaining == 0) {
                return ClosedLocalLookup(
                    current.value,
                    0,
                    semanticType = current.value.semanticType,
                )
            }
            remaining -= 1
            current = current.tail
        }
        val isProof = current is ClosedEvalEnv.Root &&
                current.localIsProof(remaining)
        val semanticType = (current as? ClosedEvalEnv.Root)?.localCtx?.getOrNull(remaining)?.let { type ->
            ClosedClosure(type.lift(remaining + 1), current)
        }
        if (current is ClosedEvalEnv.Root) remaining -= current.depth
        return ClosedLocalLookup(null, remaining, isProof, semanticType)
    }

    fun closuresObviouslyEqual(left: ClosedClosure, right: ClosedClosure): Boolean {
        if (left.isProof && right.isProof) return true
        if (left === right) return true
        if (
            left.expression === right.expression && left.locals === right.locals &&
            left.cachedValue === right.cachedValue &&
            left.pendingArguments.size == right.pendingArguments.size &&
            left.pendingArguments.indices.all { left.pendingArguments[it] === right.pendingArguments[it] }
        ) return true
        val leftBvar = left.expression as? Expression.Bvar
        val rightBvar = right.expression as? Expression.Bvar
        return leftBvar != null && rightBvar != null &&
                leftBvar.bvar == rightBvar.bvar &&
                left.locals === ClosedEvalEnv.Empty && right.locals === ClosedEvalEnv.Empty
    }

    fun referencedLooseBvars(expression: Expression): List<Int> {
        looseBvarIndices[expression.ie]?.let { return it }
        val result = mutableSetOf<Int>()
        val seen = mutableSetOf<Long>()
        val expressions = ArrayDeque<Pair<Expression, Int>>()
        expressions.addLast(expression to 0)
        while (expressions.isNotEmpty()) {
            val [current, depth] = expressions.removeLast()
            val key = (depth.toLong() shl 32) xor (current.ie.toLong() and 0xffffffffL)
            if (!seen.add(key)) continue
            when (current) {
                is Expression.Bvar -> if (current.bvar >= depth) result += current.bvar - depth
                is Expression.App -> {
                    expressions.addLast(current.fnExpr to depth)
                    expressions.addLast(current.argExpr to depth)
                }
                is Expression.ForallE -> {
                    expressions.addLast(current.typeExpr to depth)
                    expressions.addLast(current.bodyExpr to depth + 1)
                }
                is Expression.Lam -> {
                    expressions.addLast(current.typeExpr to depth)
                    expressions.addLast(current.bodyExpr to depth + 1)
                }
                is Expression.LetE -> {
                    expressions.addLast(current.typeExpr to depth)
                    expressions.addLast(current.valueExpr to depth)
                    expressions.addLast(current.bodyExpr to depth + 1)
                }
                is Expression.Mdata -> expressions.addLast(current.expr to depth)
                is Expression.Proj -> expressions.addLast(current.structExpr to depth)
                is Expression.Const, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> {}
            }
        }
        return result.sorted().also { indices -> looseBvarIndices[expression.ie] = indices }
    }

    fun enqueueEnvironmentAgreement(
        expression: Expression,
        left: ClosedEvalEnv,
        right: ClosedEvalEnv,
        nextNeutral: Int,
        fallback: ClosedDefEqFallback?,
    ): Boolean {
        for (index in referencedLooseBvars(expression)) {
            val leftLookup = bindingAt(left, index)
            val rightLookup = bindingAt(right, index)
            if (leftLookup.closure == null && rightLookup.closure == null) {
                if (leftLookup.neutralIndex != rightLookup.neutralIndex) return false
                continue
            }
            val leftBinding = leftLookup.closure ?: ClosedClosure(
                Expression.Bvar(leftLookup.neutralIndex, Int.MIN_VALUE),
                ClosedEvalEnv.Empty,
                leftLookup.isProof,
            ).also { it.semanticType = leftLookup.semanticType }
            val rightBinding = rightLookup.closure ?: ClosedClosure(
                Expression.Bvar(rightLookup.neutralIndex, Int.MIN_VALUE),
                ClosedEvalEnv.Empty,
                rightLookup.isProof,
            ).also { it.semanticType = rightLookup.semanticType }
            if (!closuresObviouslyEqual(leftBinding, rightBinding)) {
                pending.addLast(
                    ClosedDefEqTask(
                        leftBinding,
                        rightBinding,
                        nextNeutral,
                        true,
                        (leftBinding.semanticType ?: rightBinding.semanticType)
                            ?.let(ClosedExpectedType::Closure),
                        fallback,
                    )
                )
            }
        }
        return true
    }

    fun proofArgumentMask(head: Expression.Const, arity: Int): BooleanArray? {
        val key = (head.ie.toLong() shl 32) xor (arity.toLong() and 0xffffffffL)
        val proofArgumentMasks = env.semanticRuntime.proofArgumentMasks
        if (proofArgumentMasks.containsKey(key)) return proofArgumentMasks[key]
        var type = head.inferType(validate = false)
        var localCtx = emptyList<Expression>()
        val result = BooleanArray(arity)
        for (index in 0 until arity) {
            val forall = type.whnf(localCtx = localCtx) as? Expression.ForallE
                ?: return null.also { proofArgumentMasks[key] = null }
            result[index] = forall.typeExpr
                .inferSort(localCtx = localCtx, validate = false)
                .isLessOrEqual(Level.Zero)
            localCtx = env.consLocalCtx(forall.typeExpr, localCtx)
            type = forall.bodyExpr
        }
        proofArgumentMasks[key] = result
        return result
    }

    fun structureEtaInfo(value: ClosedValue): Pair<Int, Inductive.ConstructorVal>? {
        val constructorConst = value.head.expression as? Expression.Const ?: return null
        val constructor = constructorConst.decl as? Inductive.ConstructorVal ?: return null
        if (value.arguments.size != constructor.numParams + constructor.numFields) return null
        val inductiveIndex = env.nameIndices[constructor.inductName] ?: return null
        val inductive = env.declarations[inductiveIndex] as? Inductive.InductiveVal ?: return null
        if (inductive.isRec || inductive.numIndices != 0 || inductive.ctors.size != 1) return null
        var inductiveType = inductive.typeExpr.instantiateLevelParams(
            constructorConst.composeLevelSubst(emptyMap())
        )
        repeat(inductive.numParams) {
            inductiveType = (inductiveType as? Expression.ForallE)?.bodyExpr ?: return null
        }
        val resultSort = inductiveType as? Expression.Sort ?: return null
        if (resultSort.level.isLessOrEqual(Level.Zero)) return null
        return inductiveIndex to constructor
    }

    fun projectClosedValue(
        value: ClosedValue,
        inductiveIndex: Int,
        fieldIndex: Int,
        structureType: ClosedClosure? = null,
    ): ClosedClosure {
        val valueClosure = value.asClosure()
        structureType?.let(valueClosure::withSemanticType)
        val valueRef = env.addCustomExpr { Expression.Bvar(0, it) }
        val projection = env.addCustomExpr {
            Expression.Proj(typeName = inductiveIndex, idx = fieldIndex, struct = valueRef.ie, ie = it)
        }
        return ClosedClosure(
            projection,
            ClosedEvalEnv.Bind(valueClosure, ClosedEvalEnv.Empty),
        )
    }

    fun constructorStructureType(
        value: ClosedValue,
        inductiveIndex: Int,
        constructor: Inductive.ConstructorVal,
    ): ClosedClosure {
        val constructorConst = value.head.expression as Expression.Const
        val inductiveConst = env.addCustomExpr {
            Expression.Const(
                inductiveIndex,
                constructorConst.levels.map { level -> level.il },
                it,
            )
        }
        return ClosedClosure(
            inductiveConst,
            ClosedEvalEnv.Empty,
            pendingArguments = value.arguments.takeArgs(constructor.numParams),
        )
    }

    fun resolveExpectedType(expectedType: ClosedExpectedType?): ClosedClosure? {
        if (expectedType == null) return null
        if (resolvedExpectedTypes.containsKey(expectedType)) return resolvedExpectedTypes[expectedType]
        val result = when (expectedType) {
            is ClosedExpectedType.Closure -> expectedType.value
            is ClosedExpectedType.ConstantArgument -> run {
                var type = ClosedClosure(expectedType.head.inferType(validate = false), ClosedEvalEnv.Empty)
                for (index in 0..expectedType.index) {
                    val typeValue = type.closedWhnf(instantiatedRecursorRules, trace) ?: return@run null
                    if (typeValue.arguments.isNotEmpty()) return@run null
                    val forall = typeValue.head.expression as? Expression.ForallE ?: return@run null
                    if (index == expectedType.index) {
                        return@run ClosedClosure(forall.typeExpr, typeValue.head.locals)
                    }
                    val argument = expectedType.arguments.getOrNull(index) ?: return@run null
                    type = ClosedClosure(
                        forall.bodyExpr,
                        ClosedEvalEnv.Bind(
                            argument.withSemanticType(ClosedClosure(forall.typeExpr, typeValue.head.locals)),
                            typeValue.head.locals,
                        ),
                    )
                }
                null
            }
        }
        resolvedExpectedTypes[expectedType] = result
        return result
    }

    fun closureTypeIsProp(closure: ClosedClosure): Boolean {
        val value = closure.closedWhnf(
            instantiatedRecursorRules,
            trace,
            unfoldDefinitionsAtRoot = false,
        ) ?: return false
        val constant = value.head.expression as? Expression.Const ?: return false
        var type = ClosedClosure(constant.inferType(validate = false), ClosedEvalEnv.Empty)
        for (argument in value.arguments) {
            val typeValue = type.closedWhnf(instantiatedRecursorRules, trace) ?: return false
            if (typeValue.arguments.isNotEmpty()) return false
            val pi = typeValue.head.expression as? Expression.ForallE ?: return false
            type = ClosedClosure(
                pi.bodyExpr,
                ClosedEvalEnv.Bind(
                    argument.withSemanticType(ClosedClosure(pi.typeExpr, typeValue.head.locals)),
                    typeValue.head.locals,
                ),
            )
        }
        val result = type.closedWhnf(instantiatedRecursorRules, trace) ?: return false
        val sort = result.head.expression as? Expression.Sort ?: return false
        return result.arguments.isEmpty() && sort.level.isLessOrEqual(Level.Zero)
    }

    fun expectedTypeIsProp(expectedType: ClosedExpectedType?): Boolean {
        if (expectedType == null) return false
        if (expectedType is ClosedExpectedType.ConstantArgument) {
            expectedType.isProof?.let { return it }
            val arity = maxOf(expectedType.arguments.size, expectedType.index + 1)
            proofArgumentMask(expectedType.head, arity)?.let { return it[expectedType.index] }
        }
        return expectedTypePropCache.getOrPut(expectedType) {
            val expected = resolveExpectedType(expectedType) ?: return@getOrPut false
            val bvar = expected.expression as? Expression.Bvar
                ?: return@getOrPut closureTypeIsProp(expected)
            var index = bvar.bvar
            var locals = expected.locals
            while (locals is ClosedEvalEnv.Bind) {
                if (index == 0) return@getOrPut closureTypeIsProp(locals.value)
                index -= 1
                locals = locals.tail
            }
            val root = locals as? ClosedEvalEnv.Root ?: return@getOrPut false
            val binderType = root.localCtx.getOrNull(index)?.lift(index + 1)
                ?: return@getOrPut false
            val sort = binderType.whnf(localCtx = root.localCtx) as? Expression.Sort
                ?: return@getOrPut false
            sort.level.isLessOrEqual(Level.Zero)
        }
    }

    fun applyExpectedFunctionType(
        expectedType: ClosedExpectedType?,
        neutral: ClosedClosure,
    ): ClosedExpectedType? {
        val type = resolveExpectedType(expectedType) ?: return null
        val typeValue = type.closedWhnf(instantiatedRecursorRules, trace) ?: return null
        if (typeValue.arguments.isNotEmpty()) return null
        val forall = typeValue.head.expression as? Expression.ForallE ?: return null
        return ClosedExpectedType.Closure(
            ClosedClosure(
                forall.bodyExpr,
                ClosedEvalEnv.Bind(neutral, typeValue.head.locals),
            )
        )
    }

    fun argumentExpectedType(value: ClosedValue, argumentIndex: Int): ClosedExpectedType? {
        var type = value.head.semanticType ?: return null
        for (index in 0..argumentIndex) {
            val typeValue = type.closedWhnf(instantiatedRecursorRules, trace) ?: return null
            if (typeValue.arguments.isNotEmpty()) return null
            val forall = typeValue.head.expression as? Expression.ForallE ?: return null
            if (index == argumentIndex) {
                return ClosedExpectedType.Closure(
                    ClosedClosure(forall.typeExpr, typeValue.head.locals)
                )
            }
            val argument = value.arguments.getOrNull(index) ?: return null
            type = ClosedClosure(
                forall.bodyExpr,
                ClosedEvalEnv.Bind(
                    argument.withSemanticType(ClosedClosure(forall.typeExpr, typeValue.head.locals)),
                    typeValue.head.locals,
                ),
            )
        }
        return null
    }

    fun enclosingStructureType(expectedType: ClosedExpectedType?): ClosedExpectedType? {
        val argumentType = expectedType as? ClosedExpectedType.ConstantArgument ?: return null
        val constructor = argumentType.head.decl as? Inductive.ConstructorVal ?: return null
        if (
            argumentType.index !in constructor.numParams until constructor.numParams + constructor.numFields ||
            argumentType.arguments.size < constructor.numParams
        ) return null
        val inductiveIndex = env.nameIndices[constructor.inductName] ?: return null
        val inductiveConst = env.addCustomExpr {
            Expression.Const(
                inductiveIndex,
                argumentType.head.levels.map { level -> level.il },
                it,
            )
        }
        return ClosedExpectedType.Closure(
            ClosedClosure(
                inductiveConst,
                ClosedEvalEnv.Empty,
                pendingArguments = argumentType.arguments.takeArgs(constructor.numParams),
            )
        )
    }

    fun deltaStep(value: ClosedValue): Pair<LazyDeltaHeadInfo, ClosedClosure>? {
        val head = value.head.expression as? Expression.Const ?: return null
        val step = head.lazyDeltaStepInfo() ?: return null
        val unfolded = head.instantiatedValue() ?: return null
        val closure = ClosedClosure(
            unfolded,
            ClosedEvalEnv.Empty,
            pendingArguments = value.arguments,
        )
        return step to closure
    }

    fun headsCanBeCompared(left: ClosedValue, right: ClosedValue): Boolean {
        val leftHead = left.head.expression
        val rightHead = right.head.expression
        return when {
            leftHead is Expression.Const && rightHead is Expression.Const ->
                leftHead.name == rightHead.name &&
                        leftHead.levels.size == rightHead.levels.size &&
                        leftHead.levels.indices.all { index ->
                            leftHead.levels[index].isEqual(rightHead.levels[index])
                        }

            leftHead is Expression.Lam || rightHead is Expression.Lam -> true
            leftHead is Expression.ForallE && rightHead is Expression.ForallE -> true
            leftHead is Expression.Proj && rightHead is Expression.Proj -> true
            leftHead is Expression.Bvar && rightHead is Expression.Bvar -> true
            leftHead is Expression.NatVal && rightHead is Expression.NatVal -> true
            leftHead is Expression.Sort && rightHead is Expression.Sort -> true
            leftHead is Expression.StrVal && rightHead is Expression.StrVal -> true
            else -> false
        }
    }

    fun unfoldForComparison(
        leftRoot: ClosedClosure,
        rightRoot: ClosedClosure,
    ): Pair<ClosedValue, ClosedValue>? {
        var left = leftRoot.closedWhnf(instantiatedRecursorRules, trace, unfoldDefinitionsAtRoot = false)
            ?: return null
        var right = rightRoot.closedWhnf(instantiatedRecursorRules, trace, unfoldDefinitionsAtRoot = false)
            ?: return null
        var forcedLeftIota = false
        var forcedRightIota = false

        fun ClosedValue.canForceIota(): Boolean {
            val declaration = (head.expression as? Expression.Const)?.decl
            return declaration is Inductive.RecursorVal ||
                    declaration is Declaration.Quot &&
                    (declaration.kind == Declaration.Quot.Kind.Lift ||
                            declaration.kind == Declaration.Quot.Kind.Ind)
        }

        fun ClosedValue.forceIota(): ClosedValue? =
            asClosure().closedWhnf(instantiatedRecursorRules, trace)

        while (true) {
            while (!headsCanBeCompared(left, right)) {
            val leftStep = deltaStep(left)
            val rightStep = deltaStep(right)
                if (leftStep == null && rightStep == null) {
                    var forcedIota = false
                    if (!forcedLeftIota && left.canForceIota()) {
                        forcedLeftIota = true
                        left = left.forceIota() ?: return null
                        forcedIota = true
                    }
                    if (!forcedRightIota && right.canForceIota()) {
                        forcedRightIota = true
                        right = right.forceIota() ?: return null
                        forcedIota = true
                    }
                    if (forcedIota) continue
                    break
                }

            val unfoldLeft: Boolean
            val unfoldRight: Boolean
            when {
                leftStep == null -> {
                    unfoldLeft = false
                    unfoldRight = true
                }

                rightStep == null -> {
                    unfoldLeft = true
                    unfoldRight = false
                }

                leftStep.first.kind.priority != rightStep.first.kind.priority -> {
                    unfoldLeft = leftStep.first.kind.priority > rightStep.first.kind.priority
                    unfoldRight = !unfoldLeft
                }

                leftStep.first.regularHeight != rightStep.first.regularHeight -> {
                    unfoldLeft = leftStep.first.regularHeight > rightStep.first.regularHeight
                    unfoldRight = !unfoldLeft
                }

                else -> {
                    unfoldLeft = true
                    unfoldRight = true
                }
            }
            if (unfoldLeft) {
                left = leftStep!!.second.closedWhnf(
                    instantiatedRecursorRules,
                    trace,
                    unfoldDefinitionsAtRoot = false,
                ) ?: return null
            }
            if (unfoldRight) {
                right = rightStep!!.second.closedWhnf(
                    instantiatedRecursorRules,
                    trace,
                    unfoldDefinitionsAtRoot = false,
                ) ?: return null
            }
            }

            return left to right
        }
    }

    pending.addLast(
        ClosedDefEqTask(this, other, nextNeutral, expectedType != null, expectedType)
    )
    while (pending.isNotEmpty()) {
        if (
            env.semanticRuntime.activeConversions != 0 &&
            env.semanticRuntime.remainingSteps-- <= 0
        ) {
            if (trace) println("closed conversion declined: step limit")
            return false
        }
        val task = pending.removeLast()
        if (task.left.isProof && task.right.isProof) continue
        val sameClosureRepresentation =
            task.left.expression === task.right.expression &&
                    task.left.cachedValue === task.right.cachedValue &&
                    task.left.pendingArguments.size == task.right.pendingArguments.size &&
                    task.left.pendingArguments.indices.all {
                        task.left.pendingArguments[it] === task.right.pendingArguments[it]
                    }
        if (sameClosureRepresentation && task.left.locals === task.right.locals) continue
        val state = ClosedDefEqState(
            task.left.expression.ie,
            task.left.locals,
            task.left.pendingArguments,
            task.right.expression.ie,
            task.right.locals,
            task.right.pendingArguments,
            task.left.cachedValue,
            task.right.cachedValue,
            task.nextNeutral,
            task.sameTypeKnown,
            task.fallback,
        )
        if (!visited.add(state)) continue
        fun recover(): Boolean {
            val fallback = task.fallback ?: return false
            fun ClosedDefEqFallback?.contains(target: ClosedDefEqFallback): Boolean {
                var current = this
                while (current != null) {
                    if (current === target) return true
                    current = current.outer
                }
                return false
            }
            while (pending.lastOrNull()?.fallback.contains(fallback)) pending.removeLast()
            visited.clear()
            pending.addLast(fallback.alternative)
            return true
        }
        if (task.sameTypeKnown && expectedTypeIsProp(task.expectedType)) continue
        if (sameClosureRepresentation) {
            if (
                enqueueEnvironmentAgreement(
                    task.left.expression,
                    task.left.locals,
                    task.right.locals,
                    task.nextNeutral,
                    task.fallback,
                )
            ) continue else {
                if (recover()) continue
                return false
            }
        }
        val comparison = unfoldForComparison(task.left, task.right)
        if (comparison == null) {
            if (recover()) continue
            return false
        }
        val left = comparison.first
        val right = comparison.second
        if (task.sameTypeKnown && (left.head.isProof || right.head.isProof)) continue

        val leftProjection = left.projection?.descriptor
            ?: left.head.expression as? Expression.Proj
        val rightProjection = right.projection?.descriptor
            ?: right.head.expression as? Expression.Proj
        if (leftProjection != null && rightProjection != null) {
            if (left.arguments.size != right.arguments.size) {
                if (recover()) continue
                return false
            }
            if (
                leftProjection.typeNameExpr != rightProjection.typeNameExpr ||
                leftProjection.projIndex != rightProjection.projIndex
            ) {
                if (recover()) continue
                return false
            }
            val structureExpectedType = enclosingStructureType(task.expectedType)
            pending.addLast(
                ClosedDefEqTask(
                    left.projection?.structure?.asClosure()
                        ?: ClosedClosure(leftProjection.structExpr, left.head.locals),
                    right.projection?.structure?.asClosure()
                        ?: ClosedClosure(rightProjection.structExpr, right.head.locals),
                    task.nextNeutral,
                    true,
                    structureExpectedType,
                    task.fallback,
                )
            )
            for (index in left.arguments.indices) {
                pending.addLast(
                    ClosedDefEqTask(
                        left.arguments[index], right.arguments[index], task.nextNeutral, true,
                        fallback = task.fallback,
                    )
                )
            }
            continue
        }

        if (task.sameTypeKnown) {
            val leftEta = structureEtaInfo(left)
            val rightEta = structureEtaInfo(right)
            val leftIsAnyConstructor = (left.head.expression as? Expression.Const)?.decl is Inductive.ConstructorVal
            val rightIsAnyConstructor = (right.head.expression as? Expression.Const)?.decl is Inductive.ConstructorVal
            if (leftEta != null && rightEta == null && !rightIsAnyConstructor) {
                val [inductiveIndex, constructor] = leftEta
                val constructorConst = left.head.expression as Expression.Const
                val structureType = constructorStructureType(left, inductiveIndex, constructor)
                for (fieldIndex in 0 until constructor.numFields) {
                    pending.addLast(
                        ClosedDefEqTask(
                            left.arguments[constructor.numParams + fieldIndex],
                            projectClosedValue(right, inductiveIndex, fieldIndex, structureType),
                            task.nextNeutral,
                            true,
                            ClosedExpectedType.ConstantArgument(
                                constructorConst,
                                left.arguments,
                                constructor.numParams + fieldIndex,
                            ),
                            task.fallback,
                        )
                    )
                }
                continue
            }
            if (rightEta != null && leftEta == null && !leftIsAnyConstructor) {
                val [inductiveIndex, constructor] = rightEta
                val constructorConst = right.head.expression as Expression.Const
                val structureType = constructorStructureType(right, inductiveIndex, constructor)
                for (fieldIndex in 0 until constructor.numFields) {
                    pending.addLast(
                        ClosedDefEqTask(
                            projectClosedValue(left, inductiveIndex, fieldIndex, structureType),
                            right.arguments[constructor.numParams + fieldIndex],
                            task.nextNeutral,
                            true,
                            ClosedExpectedType.ConstantArgument(
                                constructorConst,
                                right.arguments,
                                constructor.numParams + fieldIndex,
                            ),
                            task.fallback,
                        )
                    )
                }
                continue
            }

        }

        val leftLambda = left.head.expression as? Expression.Lam
        val rightLambda = right.head.expression as? Expression.Lam
        if (leftLambda != null || rightLambda != null) {
            val neutralDomain = leftLambda?.typeExpr ?: checkNotNull(rightLambda).typeExpr
            val neutral = ClosedClosure(
                Expression.Bvar(task.nextNeutral, Int.MIN_VALUE),
                ClosedEvalEnv.Empty,
            ).also {
                it.semanticType = if (leftLambda != null) {
                    ClosedClosure(leftLambda.typeExpr, left.head.locals)
                } else {
                    ClosedClosure(checkNotNull(rightLambda).typeExpr, right.head.locals)
                }
            }
            fun applyNeutral(value: ClosedValue, lambda: Expression.Lam?): ClosedClosure {
                if (lambda != null) {
                    return ClosedClosure(
                        lambda.bodyExpr,
                        ClosedEvalEnv.Bind(neutral, value.head.locals),
                    )
                }
                return value.asClosure(value.arguments.append(neutral))
            }
            pending.addLast(
                ClosedDefEqTask(
                    applyNeutral(left, leftLambda),
                    applyNeutral(right, rightLambda),
                    task.nextNeutral - 1,
                    true,
                    applyExpectedFunctionType(task.expectedType, neutral),
                    task.fallback,
                )
            )
            if (leftLambda != null && rightLambda != null) {
                pending.addLast(
                    ClosedDefEqTask(
                        ClosedClosure(leftLambda.typeExpr, left.head.locals),
                        ClosedClosure(rightLambda.typeExpr, right.head.locals),
                        task.nextNeutral,
                        true,
                        fallback = task.fallback,
                    )
                )
            }
            continue
        }


        if (task.sameTypeKnown) {
            val expectedType = resolveExpectedType(task.expectedType)
            val typeValue = expectedType?.closedWhnf(instantiatedRecursorRules, trace)
            val forall = typeValue?.head?.expression as? Expression.ForallE
            if (forall != null && typeValue.arguments.isEmpty()) {
                val neutral = ClosedClosure(
                    Expression.Bvar(task.nextNeutral, Int.MIN_VALUE),
                    ClosedEvalEnv.Empty,
                ).also {
                    it.semanticType = ClosedClosure(forall.typeExpr, typeValue.head.locals)
                }

                fun applyNeutral(value: ClosedValue): ClosedClosure =
                    value.asClosure(value.arguments.append(neutral))
                pending.addLast(
                    ClosedDefEqTask(
                        applyNeutral(left),
                        applyNeutral(right),
                        task.nextNeutral - 1,
                        true,
                        ClosedExpectedType.Closure(
                            ClosedClosure(
                                forall.bodyExpr,
                                ClosedEvalEnv.Bind(neutral, typeValue.head.locals),
                            )
                        ),
                        task.fallback,
                    )
                )
                continue
            }
        }

        fun ClosedValue.natValueOrNull(): NatValue? {
            if (this.arguments.isNotEmpty()) return null
            return when (val expression = this.head.expression) {
                is Expression.NatVal -> expression.natVal
                else -> if (expression.isNatZeroCtorConst()) NatValue.ZERO else null
            }
        }

        fun ClosedValue.natPredecessorOrNull(): ClosedClosure? {
            val literal = natValueOrNull()
            if (literal != null) {
                if (literal.isZero()) return null
                return ClosedClosure(
                    Expression.NatVal(literal - NatValue.ONE, Int.MIN_VALUE),
                    ClosedEvalEnv.Empty,
                )
            }
            val constant = head.expression as? Expression.Const ?: return null
            if (
                constant.levels.isNotEmpty() ||
                constant.name.toStringDetailed() != "Nat.succ" ||
                arguments.size != 1
            ) return null
            return arguments[0]
        }

        val leftNat = left.natValueOrNull()
        val rightNat = right.natValueOrNull()
        if (leftNat != null || rightNat != null) {
            if (leftNat != null && rightNat != null) {
                if (leftNat != rightNat) {
                    if (recover()) continue
                    return false
                }
                continue
            }
            val leftPred = left.natPredecessorOrNull()
            val rightPred = right.natPredecessorOrNull()
            if (leftPred == null || rightPred == null) {
                if (recover()) continue
                return false
            }
            pending.addLast(
                ClosedDefEqTask(
                    leftPred,
                    rightPred,
                    task.nextNeutral,
                    true,
                    fallback = task.fallback,
                )
            )
            continue
        }

        if (left.arguments.size != right.arguments.size) {
            if (recover()) continue
            return false
        }

        val leftForall = left.head.expression as? Expression.ForallE
        val rightForall = right.head.expression as? Expression.ForallE
        if (leftForall != null && rightForall != null && left.arguments.isEmpty()) {
            val neutral = ClosedClosure(
                Expression.Bvar(task.nextNeutral, Int.MIN_VALUE),
                ClosedEvalEnv.Empty,
            ).also {
                it.semanticType = ClosedClosure(leftForall.typeExpr, left.head.locals)
            }
            pending.addLast(
                ClosedDefEqTask(
                    ClosedClosure(
                        leftForall.bodyExpr,
                        ClosedEvalEnv.Bind(neutral, left.head.locals),
                    ),
                    ClosedClosure(
                        rightForall.bodyExpr,
                        ClosedEvalEnv.Bind(neutral, right.head.locals),
                    ),
                    task.nextNeutral - 1,
                    true,
                    fallback = task.fallback,
                )
            )
            pending.addLast(
                ClosedDefEqTask(
                    ClosedClosure(leftForall.typeExpr, left.head.locals),
                    ClosedClosure(rightForall.typeExpr, right.head.locals),
                    task.nextNeutral,
                    true,
                    fallback = task.fallback,
                )
            )
            continue
        }

        val leftHead = left.head.expression
        val rightHead = right.head.expression
        val headsMatch = when {
            leftHead is Expression.Const && rightHead is Expression.Const ->
                leftHead.name == rightHead.name &&
                        leftHead.levels.size == rightHead.levels.size &&
                        leftHead.levels.indices.all { index ->
                            leftHead.levels[index].isEqual(rightHead.levels[index])
                        }

            leftHead is Expression.Sort && rightHead is Expression.Sort ->
                leftHead.level.isEqual(rightHead.level)

            leftHead is Expression.StrVal && rightHead is Expression.StrVal ->
                leftHead.strVal == rightHead.strVal

            leftHead is Expression.Bvar && rightHead is Expression.Bvar ->
                leftHead.bvar == rightHead.bvar

            else -> false
        }
        if (!headsMatch) {
            if (recover()) continue
            return false
        }
        if (leftHead !is Expression.Const && task.sameTypeKnown) {
            resolveExpectedType(task.expectedType)?.let { type ->
                if (left.head.semanticType == null) left.head.semanticType = type
                if (right.head.semanticType == null) right.head.semanticType = type
            }
        }
        var tryCongruenceBeforeDelta = false
        val deltaAlternative = if (
            leftHead is Expression.Const &&
            rightHead is Expression.Const &&
            left.arguments.isNotEmpty()
        ) {
            val leftStep = deltaStep(left)
            val rightStep = deltaStep(right)
            if (leftStep == null && rightStep == null) {
                null
            } else {
                tryCongruenceBeforeDelta =
                    leftStep?.first?.kind == LazyDeltaStepKind.Regular &&
                            rightStep?.first?.kind == LazyDeltaStepKind.Regular
                val unfoldLeft: Boolean
                val unfoldRight: Boolean
                when {
                    leftStep == null -> {
                        unfoldLeft = false
                        unfoldRight = true
                    }

                    rightStep == null -> {
                        unfoldLeft = true
                        unfoldRight = false
                    }

                    leftStep.first.kind.priority != rightStep.first.kind.priority -> {
                        unfoldLeft = leftStep.first.kind.priority > rightStep.first.kind.priority
                        unfoldRight = !unfoldLeft
                    }

                    leftStep.first.regularHeight != rightStep.first.regularHeight -> {
                        unfoldLeft = leftStep.first.regularHeight > rightStep.first.regularHeight
                        unfoldRight = !unfoldLeft
                    }

                    else -> {
                        unfoldLeft = true
                        unfoldRight = true
                    }
                }
                ClosedDefEqTask(
                    if (unfoldLeft) leftStep!!.second else left.asClosure(),
                    if (unfoldRight) rightStep!!.second else right.asClosure(),
                    task.nextNeutral,
                    task.sameTypeKnown,
                    task.expectedType,
                    task.fallback,
                )
            }
        } else {
            null
        }
        if (deltaAlternative != null && !tryCongruenceBeforeDelta) {
            pending.addLast(deltaAlternative)
            continue
        }
        val comparisonFallback = if (deltaAlternative == null) {
            task.fallback
        } else {
            ClosedDefEqFallback(
                deltaAlternative,
                task.fallback,
            )
        }
        val proofArguments = (leftHead as? Expression.Const)?.takeIf {
            left.arguments.isNotEmpty()
        }?.let {
            proofArgumentMask(it, left.arguments.size)
        }
        for (index in left.arguments.indices) {
            if (proofArguments?.get(index) == true) continue
            val expectedType = (leftHead as? Expression.Const)?.let { head ->
                ClosedExpectedType.ConstantArgument(
                    head,
                    left.arguments,
                    index,
                    isProof = false,
                )
            } ?: argumentExpectedType(left, index)
            pending.addLast(
                ClosedDefEqTask(
                    left.arguments[index],
                    right.arguments[index],
                    task.nextNeutral,
                    true,
                    expectedType,
                    comparisonFallback,
                )
            )
        }
    }
    return true
}

context(env: Environment)
private fun Expression.closedDefEq(other: Expression): Boolean {
    if (this.maxLooseBVarIndex() >= 0 || other.maxLooseBVarIndex() >= 0) return false
    return ClosedClosure(this, ClosedEvalEnv.Empty).closedDefEq(
        ClosedClosure(other, ClosedEvalEnv.Empty)
    )
}

private data class ClosedEvalMachineState(
    val expression: Expression,
    val locals: ClosedEvalEnv,
    val arguments: ClosedArgs,
)

context(env: Environment)
private fun ClosedClosure.closedWhnf(
    instantiatedRecursorRules: MutableMap<ClosedRecursorRuleKey, Expression> =
        env.semanticRuntime.instantiatedRecursorRules,
    trace: Boolean = false,
    unfoldDefinitionsAtRoot: Boolean = true,
): ClosedValue? {
    cachedValue?.let { return it }
    val cacheable = (
            expression.ie >= 0 &&
                    pendingArguments.isEmpty() &&
                    cachedArguments == null
            )
    val isClosed = cacheable && expression.maxLooseBVarIndex() < 0
    val closedCacheKey = if (isClosed) {
        ClosedEvalCacheKey(expression.ie, unfoldDefinitionsAtRoot)
    } else null
    closedCacheKey?.let { env.semanticRuntime.closedValues[it] }?.let { return it }
    val initialArguments = this.cachedArguments ?: this.pendingArguments

    var currentExpression = this.expression
    var currentLocals = if (isClosed) ClosedEvalEnv.Empty else this.locals
    var currentIsProof = this.isProof
    var currentSemanticType = this.semanticType
    var currentProjection: ClosedProjection? = null
    var argumentStack = initialArguments
    val continuations = mutableListOf<ClosedEvalContinuation>()
//    var applications = 0L
//    var betaReductions = 0L
//    var deltaReductions = 0L
//    var recursorReductions = 0L
    var currentIsWhnf = false
    var unfoldDefinitions = unfoldDefinitionsAtRoot
//    val deltaCounts = if (debugClosedEvaluation) mutableMapOf<Name, Long>() else null
//    val recursorCounts = if (debugClosedEvaluation) mutableMapOf<Name, Long>() else null

    fun fail(reason: String): ClosedValue? {
        if (debugTargetDeclaration) println("debug evaluator stuck: $reason")
        return null
    }

    fun incrementCount(counts: MutableMap<Name, Long>?, name: Name) {
        if (counts != null) counts[name] = (counts[name] ?: 0L) + 1L
    }

    fun lookupLocal(locals: ClosedEvalEnv, index: Int): ClosedLocalLookup {
        var currentLocals = locals
        var remaining = index
        while (currentLocals is ClosedEvalEnv.Bind) {
            if (remaining == 0) return ClosedLocalLookup(currentLocals.value, 0)
            remaining -= 1
            currentLocals = currentLocals.tail
        }
        val isProof = currentLocals is ClosedEvalEnv.Root &&
                currentLocals.localIsProof(remaining)
        val semanticType = (currentLocals as? ClosedEvalEnv.Root)
            ?.localCtx?.getOrNull(remaining)?.let { type ->
                ClosedClosure(type.lift(remaining + 1), currentLocals)
            }
        if (currentLocals is ClosedEvalEnv.Root) remaining -= currentLocals.depth
        return ClosedLocalLookup(null, remaining, isProof, semanticType)
    }

    fun terminalNatValue(expression: Expression, arguments: ClosedArgs): NatValue? {
        if (arguments.isNotEmpty()) return null
        return when (expression) {
            is Expression.NatVal -> expression.natVal
            else -> if (expression.isNatZeroCtorConst()) NatValue.ZERO else null
        }
    }

    fun transientNat(value: NatValue): Expression.NatVal =
        Expression.NatVal(value, Int.MIN_VALUE)

    fun reduceNatPrimitive(primitive: ClosedNatPrimitive, values: List<NatValue>): Expression? = when (primitive) {
        ClosedNatPrimitive.Succ -> transientNat(values[0] + NatValue.ONE)
        ClosedNatPrimitive.Add -> transientNat(values[0] + values[1])
        ClosedNatPrimitive.Sub ->
            transientNat(if (values[0] >= values[1]) values[0] - values[1] else NatValue.ZERO)

        ClosedNatPrimitive.Mul -> transientNat(values[0] * values[1])
        ClosedNatPrimitive.Pow -> {
            val exponent = values[1].toIntOrNull() ?: return null
            transientNat(values[0].pow(exponent))
        }
        ClosedNatPrimitive.Div -> transientNat(values[0].divLean(values[1]))
        ClosedNatPrimitive.Mod -> transientNat(values[0].modLean(values[1]))
        ClosedNatPrimitive.Beq -> boolCtor(values[0] == values[1])
        ClosedNatPrimitive.Ble -> boolCtor(values[0] <= values[1])
    }

    fun tryKRule(
        recursorConst: Expression.Const,
        recursor: Inductive.RecursorVal,
        recursorArgs: ClosedArgs,
    ): Inductive.RecursorVal.RecursorRule? {
        fun fail(reason: String): Inductive.RecursorVal.RecursorRule? {
            if (debugClosedEvaluation || trace) {
                println("closed K declined: ${recursorConst.name.toStringDetailed()} $reason")
            }
            return null
        }
        if (!recursor.k) return null
        val rule = recursor.rules.singleOrNull() ?: return fail("rule count")
        if (rule.nfields != 0) return fail("rule fields")
        val constructor = env.constructorByName[rule.ctorName] ?: return fail("constructor")
        if (constructor.numFields != 0 || constructor.numParams != recursor.numParams) {
            return fail("constructor shape")
        }
        val prefixSize = recursor.numParams + recursor.numMotives + recursor.numMinors
        val majorIndex = prefixSize + recursor.numIndices
        if (majorIndex >= recursorArgs.size) return fail("major index")

        val levelSubst = recursorConst.composeLevelSubst(emptyMap())
        var constructorResult = ClosedClosure(
            constructor.typeExpr.instantiateLevelParams(levelSubst),
            ClosedEvalEnv.Empty,
        )
        repeat(recursor.numParams) { parameterIndex ->
            val forall = constructorResult.expression as? Expression.ForallE ?: return fail("constructor parameter")
            val argument = recursorArgs[parameterIndex].withSemanticType(
                ClosedClosure(forall.typeExpr, constructorResult.locals)
            )
            constructorResult = ClosedClosure(
                forall.bodyExpr,
                ClosedEvalEnv.Bind(argument, constructorResult.locals),
            )
        }

        val resultType = constructorResult.closedWhnf(instantiatedRecursorRules)
            ?: return fail("constructor result reduction")
        val resultHead = resultType.head.expression as? Expression.Const ?: return fail("constructor result head")
        if (resultHead.name != constructor.inductName) return fail("constructor result inductive")
        val actualTypeArgs = recursorArgs.take(recursor.numParams) +
                recursorArgs.dropArgs(prefixSize).takeArgs(majorIndex - prefixSize)
        if (resultType.arguments.size != actualTypeArgs.size) return fail("constructor result arity")
        resultType.arguments.indices.forEach { index ->
            if (
                !resultType.arguments[index].closedDefEq(
                    actualTypeArgs[index],
                    trace = trace,
                    expectedType = ClosedExpectedType.ConstantArgument(
                        resultHead,
                        resultType.arguments,
                        index,
                    ),
                )
            ) {
                return fail("type argument $index")
            }
        }
        if (debugClosedEvaluation || trace) println("closed K reduced: ${recursorConst.name.toStringDetailed()}")
        return rule
    }

    fun applyRecursorRule(
        recursorConst: Expression.Const,
        recursor: Inductive.RecursorVal,
        recursorArgs: ClosedArgs,
        rule: Inductive.RecursorVal.RecursorRule,
        fieldArgs: List<ClosedClosure>,
    ): ClosedEvalMachineState {
        val prefixSize = recursor.numParams + recursor.numMotives + recursor.numMinors
        val majorIndex = prefixSize + recursor.numIndices
        val cacheKey = ClosedRecursorRuleKey(
            recursorConst.name,
            recursorConst.levels.map { it.il },
            rule.rhsExpr.ie,
        )
        var resultExpression = instantiatedRecursorRules.getOrPut(cacheKey) {
            val levelSubst = recursorConst.composeLevelSubst(emptyMap())
            rule.rhsExpr.instantiateLevelParams(levelSubst)
        }
        var resultLocals: ClosedEvalEnv = ClosedEvalEnv.Empty
        var resultArguments: ClosedArgs = ClosedArgs.Empty
        val ruleArguments = recursorArgs.takeArgs(prefixSize)
            .concat(ClosedArgs.fromList(fieldArgs))
            .concat(recursorArgs.dropArgs(majorIndex + 1))
        for (argument in ruleArguments) {
            val lambda = resultExpression as? Expression.Lam
            if (lambda != null && resultArguments.isEmpty()) {
                if (argument.semanticType == null) {
                    argument.semanticType = ClosedClosure(lambda.typeExpr, resultLocals)
                }
                if (
                    env.semanticRuntime.activeConversions == 0 &&
                    lambda.typeExpr.rigidTypeIsProp()
                ) argument.isProof = true
//                betaReductions += 1
                resultExpression = lambda.bodyExpr
                resultLocals = ClosedEvalEnv.Bind(argument, resultLocals)
            } else {
                resultArguments = resultArguments.append(argument)
            }
        }
        return ClosedEvalMachineState(resultExpression, resultLocals, resultArguments)
    }

    while (true) {
        if (env.semanticRuntime.activeConversions != 0) {
            if (env.semanticRuntime.remainingSteps-- <= 0) {
                return null
            }
        }
//        steps += 1
        if (currentIsWhnf) {
            currentIsWhnf = false
        } else when (val expression = currentExpression) {
            is Expression.App -> {
//                applications += 1
                argumentStack = argumentStack.prepend(ClosedClosure(expression.argExpr, currentLocals))
                currentExpression = expression.fnExpr
                continue
            }

            is Expression.Bvar -> {
                val lookup = lookupLocal(currentLocals, expression.bvar)
                val binding = lookup.closure
                if (binding == null) {
                    currentExpression = Expression.Bvar(lookup.neutralIndex, Int.MIN_VALUE)
                    currentLocals = ClosedEvalEnv.Empty
                    currentIsProof = lookup.isProof
                    currentSemanticType = lookup.semanticType
                } else {
                    val cachedValue = binding.cachedValue
                    val cachedArguments = binding.cachedArguments
                    if (cachedValue != null) {
                        currentExpression = cachedValue.head.expression
                        currentLocals = cachedValue.head.locals
                        currentIsProof = cachedValue.head.isProof
                        currentSemanticType = cachedValue.head.semanticType
                        currentProjection = cachedValue.projection
                        currentIsWhnf = argumentStack.isEmpty() || cachedValue.projection != null
                        argumentStack = cachedValue.arguments.concat(argumentStack)
                    } else if (cachedArguments == null) {
                        continuations += ClosedEvalContinuation.Force(binding, argumentStack)
                        currentExpression = binding.expression
                        currentLocals = binding.locals
                        currentIsProof = binding.isProof
                        currentSemanticType = binding.semanticType
                        argumentStack = binding.pendingArguments
                    } else {
                        currentExpression = binding.expression
                        currentLocals = binding.locals
                        currentIsProof = binding.isProof
                        currentSemanticType = binding.semanticType
                        argumentStack = cachedArguments.concat(argumentStack)
                    }
                    continue
                }
            }

            is Expression.Lam -> {
                if (argumentStack.isNotEmpty()) {
//                    betaReductions += 1
                    val argument = argumentStack[0]
                    argumentStack = argumentStack.dropArgs(1)
                    if (argument.semanticType == null) {
                        argument.semanticType = ClosedClosure(expression.typeExpr, currentLocals)
                    }
                    if (
                        env.semanticRuntime.activeConversions == 0 &&
                        expression.typeExpr.rigidTypeIsProp()
                    ) argument.isProof = true
                    currentExpression = expression.bodyExpr
                    currentLocals = ClosedEvalEnv.Bind(argument, currentLocals)
                    continue
                }
            }

            is Expression.LetE -> {
                val value = ClosedClosure(
                    expression.valueExpr,
                    currentLocals,
                    env.semanticRuntime.activeConversions == 0 &&
                            expression.typeExpr.rigidTypeIsProp(),
                ).also {
                    it.semanticType = ClosedClosure(expression.typeExpr, currentLocals)
                }
                currentExpression = expression.bodyExpr
                currentLocals = ClosedEvalEnv.Bind(value, currentLocals)
                continue
            }

            is Expression.Mdata -> {
                currentExpression = expression.expr
                continue
            }

            is Expression.Proj -> {
                continuations += ClosedEvalContinuation.Projection(
                    expression,
                    currentLocals,
                    argumentStack,
                    unfoldDefinitions,
                    currentSemanticType,
                )
                currentExpression = expression.structExpr
                argumentStack = ClosedArgs.Empty
                unfoldDefinitions = true
                continue
            }

            is Expression.Const -> {
                val quotient = expression.decl as? Declaration.Quot
                if (
                    unfoldDefinitions &&
                    quotient != null &&
                    (quotient.kind == Declaration.Quot.Kind.Lift ||
                            quotient.kind == Declaration.Quot.Kind.Ind)
                ) {
                    val arity = quotient.typeExpr.forallBinderCount()
                    if (arity > 0 && argumentStack.size >= arity) {
                        val arguments = argumentStack
                        continuations += ClosedEvalContinuation.Quotient(
                            expression,
                            quotient,
                            arguments,
                            arity,
                            unfoldDefinitions,
                        )
                        val major = arguments[arity - 1]
                        val majorValue = major.cachedValue
                        if (majorValue == null) {
                            currentExpression = major.expression
                            currentLocals = major.locals
                            currentIsProof = major.isProof
                            currentSemanticType = major.semanticType
                            currentProjection = null
                            argumentStack = major.cachedArguments ?: major.pendingArguments
                            currentIsWhnf = false
                        } else {
                            currentExpression = majorValue.head.expression
                            currentLocals = majorValue.head.locals
                            currentIsProof = majorValue.head.isProof
                            currentSemanticType = majorValue.head.semanticType
                            currentProjection = majorValue.projection
                            argumentStack = majorValue.arguments
                            currentIsWhnf = true
                        }
                        unfoldDefinitions = true
                        continue
                    }
                }

                val recursor = expression.decl as? Inductive.RecursorVal
                if (unfoldDefinitions && recursor != null) {
                    val majorIndex = recursor.numParams + recursor.numMotives +
                            recursor.numMinors + recursor.numIndices
                    if (majorIndex < argumentStack.size) {
                        val arguments = argumentStack
                        val major = arguments[majorIndex]
                        val directMajorConstructor =
                            (major.expression as? Expression.Const)?.decl is Inductive.ConstructorVal
                        val previewMajorConstructor = if (recursor.k && !directMajorConstructor) {
                            major.closedWhnf(
                                instantiatedRecursorRules,
                                trace,
                                unfoldDefinitionsAtRoot = false,
                            )?.let { value ->
                                (value.head.expression as? Expression.Const)?.decl is Inductive.ConstructorVal
                            } == true
                        } else {
                            directMajorConstructor
                        }
                        val kRule = if (recursor.k && !previewMajorConstructor) {
                            tryKRule(expression, recursor, arguments)
                        } else {
                            null
                        }
                        if (kRule != null) {
                            val state = applyRecursorRule(expression, recursor, arguments, kRule, emptyList())
                            currentExpression = state.expression
                            currentLocals = state.locals
                            argumentStack = state.arguments
                            continue
                        }
                        continuations += ClosedEvalContinuation.Recursor(
                            expression,
                            recursor,
                            arguments,
                            unfoldDefinitions,
                        )
                        val majorValue = major.cachedValue
                        if (majorValue == null) {
                            currentExpression = major.expression
                            currentLocals = major.locals
                            currentIsProof = major.isProof
                            currentSemanticType = major.semanticType
                            currentProjection = null
                            argumentStack = major.cachedArguments ?: major.pendingArguments
                            currentIsWhnf = false
                        } else {
                            currentExpression = majorValue.head.expression
                            currentLocals = majorValue.head.locals
                            currentIsProof = majorValue.head.isProof
                            currentSemanticType = majorValue.head.semanticType
                            currentProjection = majorValue.projection
                            argumentStack = majorValue.arguments
                            currentIsWhnf = true
                        }
                        unfoldDefinitions = true
                        continue
                    }
                }

                val primitive = if (unfoldDefinitions) expression.closedNatPrimitive() else null
                if (primitive != null && argumentStack.size >= primitive.arity) {
                    val arguments = argumentStack
                    val operands = arguments.takeArgs(primitive.arity)
                    continuations += ClosedEvalContinuation.NatOperand(
                        primitiveConst = expression,
                        primitive = primitive,
                        operands = operands,
                        extraArgs = arguments.dropArgs(primitive.arity),
                        values = emptyList(),
                        operandIndex = 0,
                    )
                    val operand = operands.first()
                    val operandValue = operand.cachedValue
                    if (operandValue == null) {
                        currentExpression = operand.expression
                        currentLocals = operand.locals
                        currentIsProof = operand.isProof
                        currentSemanticType = operand.semanticType
                        currentProjection = null
                        argumentStack = operand.cachedArguments ?: operand.pendingArguments
                        currentIsWhnf = false
                    } else {
                        currentExpression = operandValue.head.expression
                        currentLocals = operandValue.head.locals
                        currentIsProof = operandValue.head.isProof
                        currentSemanticType = operandValue.head.semanticType
                        currentProjection = operandValue.projection
                        argumentStack = operandValue.arguments
                        currentIsWhnf = true
                    }
                    continue
                }

                if (unfoldDefinitions) expression.instantiatedValue()?.let { definitionValue ->
//                    deltaReductions += 1
//                    incrementCount(deltaCounts, expression.name)
                    currentExpression = definitionValue
                    currentLocals = ClosedEvalEnv.Empty
                    continue
                }
            }

            is Expression.ForallE, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> {}
        }

        if (continuations.isEmpty()) {
//            if (debugClosedEvaluation) {
//                println(
//                    "closed WHNF: root=${this.expression.ie} steps=$steps apps=$applications " +
//                            "beta=$betaReductions delta=$deltaReductions recursor=$recursorReductions"
//                )
//                if (steps >= 1_000_000) {
//                    println(
//                        "  delta: " + deltaCounts.orEmpty().entries.sortedByDescending { it.value }.take(8)
//                            .joinToString { "${it.key.toStringDetailed()}=${it.value}" }
//                    )
//                    println(
//                        "  recursors: " + recursorCounts.orEmpty().entries.sortedByDescending { it.value }.take(8)
//                            .joinToString { "${it.key.toStringDetailed()}=${it.value}" }
//                    )
//                }
//            }
            return ClosedValue(
                currentExpression,
                currentLocals,
                currentIsProof,
                argumentStack,
                currentSemanticType,
                currentProjection,
            ).also { value ->
                if (closedCacheKey != null) env.semanticRuntime.closedValues[closedCacheKey] = value
            }
        }

        when (val continuation = continuations.removeAt(continuations.lastIndex)) {
            is ClosedEvalContinuation.Force -> {
                val valueArguments = argumentStack
                continuation.closure.expression = currentExpression
                continuation.closure.locals = currentLocals
                continuation.closure.cachedArguments = valueArguments
                if (currentProjection != null) {
                    continuation.closure.cachedValue = ClosedValue(
                        currentExpression,
                        currentLocals,
                        currentIsProof,
                        valueArguments,
                        currentSemanticType,
                        currentProjection,
                    )
                }
                argumentStack = valueArguments.concat(continuation.outerArgs)
            }

            is ClosedEvalContinuation.Projection -> {
                unfoldDefinitions = continuation.unfoldDefinitions
                if (currentExpression is Expression.StrVal) {
                    val constructor = currentExpression.tryStringLitCtor() ?: return fail("string projection")
                    continuations += continuation
                    currentExpression = constructor
                    currentLocals = ClosedEvalEnv.Empty
                    argumentStack = ClosedArgs.Empty
                    unfoldDefinitions = true
                    continue
                }
                val head = currentExpression as? Expression.Const
                val constructor = head?.decl as? Inductive.ConstructorVal
                if (head == null || constructor == null) {
                    val structure = ClosedValue(
                        currentExpression,
                        currentLocals,
                        currentIsProof,
                        argumentStack,
                        currentSemanticType,
                        currentProjection,
                    )
                    currentExpression = continuation.projection
                    currentLocals = continuation.locals
                    currentSemanticType = continuation.semanticType
                    currentProjection = ClosedProjection(continuation.projection, structure)
                    argumentStack = continuation.outerArgs
                    currentIsWhnf = true
                    continue
                }
                if (constructor.inductName != continuation.projection.typeNameExpr) return fail("projection type")
                val fieldIndex = constructor.numParams + continuation.projection.projIndex
                val field = argumentStack.getOrNull(fieldIndex) ?: return fail("projection field")
                if (field.semanticType == null) field.semanticType = continuation.semanticType
                val fieldValue = field.cachedValue
                if (fieldValue == null) {
                    currentExpression = field.expression
                    currentLocals = field.locals
                    currentIsProof = field.isProof
                    currentSemanticType = field.semanticType
                    currentProjection = null
                    argumentStack = (field.cachedArguments ?: field.pendingArguments)
                        .concat(continuation.outerArgs)
                    currentIsWhnf = false
                } else {
                    currentExpression = fieldValue.head.expression
                    currentLocals = fieldValue.head.locals
                    currentIsProof = fieldValue.head.isProof
                    currentSemanticType = fieldValue.head.semanticType
                    currentProjection = fieldValue.projection
                    argumentStack = fieldValue.arguments.concat(continuation.outerArgs)
                    currentIsWhnf = continuation.outerArgs.isEmpty() || fieldValue.projection != null
                }
            }

            is ClosedEvalContinuation.Quotient -> {
                unfoldDefinitions = continuation.unfoldDefinitions
                val majorHead = currentExpression as? Expression.Const
                val majorCtor = majorHead?.decl as? Declaration.Quot
                if (majorHead == null || majorCtor?.kind != Declaration.Quot.Kind.Ctor) {
                    currentExpression = continuation.quotConst
                    currentLocals = ClosedEvalEnv.Empty
                    currentProjection = null
                    argumentStack = continuation.arguments
                    currentIsWhnf = true
                    continue
                }
                val ctorArity = majorCtor.typeExpr.forallBinderCount()
                val ctorValue = argumentStack.getOrNull(ctorArity - 1) ?: return fail("quotient constructor")
                val functionIndex = when (continuation.quotient.kind) {
                    Declaration.Quot.Kind.Lift -> continuation.arity - 3
                    Declaration.Quot.Kind.Ind -> continuation.arity - 2
                    else -> return fail("quotient kind")
                }
                val function = continuation.arguments.getOrNull(functionIndex)
                    ?: return fail("quotient function")
                val extraArguments = ClosedArgs.Empty.append(ctorValue)
                    .concat(continuation.arguments.dropArgs(continuation.arity))
                val functionValue = function.cachedValue
                if (functionValue == null) {
                    currentExpression = function.expression
                    currentLocals = function.locals
                    currentIsProof = function.isProof
                    currentSemanticType = function.semanticType
                    currentProjection = null
                    argumentStack = (function.cachedArguments ?: function.pendingArguments)
                        .concat(extraArguments)
                    currentIsWhnf = false
                } else {
                    currentExpression = functionValue.head.expression
                    currentLocals = functionValue.head.locals
                    currentIsProof = functionValue.head.isProof
                    currentSemanticType = functionValue.head.semanticType
                    currentProjection = functionValue.projection
                    argumentStack = functionValue.arguments.concat(extraArguments)
                    currentIsWhnf = extraArguments.isEmpty() || functionValue.projection != null
                }
            }

            is ClosedEvalContinuation.Recursor -> {
                unfoldDefinitions = continuation.unfoldDefinitions
//                recursorReductions += 1
//                incrementCount(recursorCounts, continuation.recursorConst.name)
                val majorNat = terminalNatValue(currentExpression, argumentStack)
                val rule: Inductive.RecursorVal.RecursorRule
                val fieldArgs: List<ClosedClosure>
                if (majorNat != null) {
                    val natRules = continuation.recursor.natLiteralRecursorRules() ?: return fail("Nat recursor rules")
                    if (majorNat.isZero()) {
                        rule = natRules.zeroRule
                        fieldArgs = emptyList()
                    } else {
                        rule = natRules.succRule
                        val predecessor = transientNat(majorNat - NatValue.ONE)
                        fieldArgs = listOf(ClosedClosure(predecessor, ClosedEvalEnv.Empty))
                    }
                } else {
                    if (currentExpression is Expression.StrVal) {
                        val constructor = currentExpression.tryStringLitCtor() ?: return fail("string recursor")
                        continuations += continuation
                        currentExpression = constructor
                        currentLocals = ClosedEvalEnv.Empty
                        argumentStack = ClosedArgs.Empty
                        unfoldDefinitions = true
                        continue
                    }
                    val majorHead = currentExpression as? Expression.Const
                    val constructor = majorHead?.decl as? Inductive.ConstructorVal
                    if (majorHead == null || constructor == null) {
                        currentExpression = continuation.recursorConst
                        currentLocals = ClosedEvalEnv.Empty
                        currentProjection = null
                        argumentStack = continuation.recursorArgs
                        currentIsWhnf = true
                        continue
                    }
                    rule = continuation.recursor.rules.singleOrNull { it.ctorName == majorHead.name }
                        ?: return fail("recursor rule")
                    if (constructor.numFields != rule.nfields) return fail("recursor fields")
                    val majorArgs = argumentStack
                    if (majorArgs.size != constructor.numParams + constructor.numFields) {
                        return fail("recursor arity")
                    }
                    fieldArgs = majorArgs.drop(constructor.numParams)
                }
                val state = applyRecursorRule(
                    continuation.recursorConst,
                    continuation.recursor,
                    continuation.recursorArgs,
                    rule,
                    fieldArgs,
                )
                currentExpression = state.expression
                currentLocals = state.locals
                currentProjection = null
                argumentStack = state.arguments
            }

            is ClosedEvalContinuation.NatOperand -> {
                val value = terminalNatValue(currentExpression, argumentStack)
                if (value == null) {
                    val definitionValue = continuation.primitiveConst.instantiatedValue()
                    if (definitionValue == null) {
                        currentExpression = continuation.primitiveConst
                        currentLocals = ClosedEvalEnv.Empty
                        currentProjection = null
                        argumentStack = continuation.operands.concat(continuation.extraArgs)
                        currentIsWhnf = true
                    } else {
//                        deltaReductions += 1
//                        incrementCount(deltaCounts, continuation.primitiveConst.name)
                        currentExpression = definitionValue
                        currentLocals = ClosedEvalEnv.Empty
                        currentProjection = null
                        argumentStack = continuation.operands.concat(continuation.extraArgs)
                    }
                    continue
                }
                val values = continuation.values + value
                val nextIndex = continuation.operandIndex + 1
                if (nextIndex < continuation.operands.size) {
                    continuations += continuation.copy(values = values, operandIndex = nextIndex)
                    val operand = continuation.operands[nextIndex]
                    val operandValue = operand.cachedValue
                    if (operandValue == null) {
                        currentExpression = operand.expression
                        currentLocals = operand.locals
                        currentIsProof = operand.isProof
                        currentSemanticType = operand.semanticType
                        currentProjection = null
                        argumentStack = operand.cachedArguments ?: operand.pendingArguments
                        currentIsWhnf = false
                    } else {
                        currentExpression = operandValue.head.expression
                        currentLocals = operandValue.head.locals
                        currentIsProof = operandValue.head.isProof
                        currentSemanticType = operandValue.head.semanticType
                        currentProjection = operandValue.projection
                        argumentStack = operandValue.arguments
                        currentIsWhnf = true
                    }
                } else {
                    val reduced = reduceNatPrimitive(continuation.primitive, values)
                    if (reduced == null) {
                        val definitionValue = continuation.primitiveConst.instantiatedValue()
                        if (definitionValue == null) {
                            currentExpression = continuation.primitiveConst
                            currentLocals = ClosedEvalEnv.Empty
                            currentProjection = null
                            argumentStack = continuation.operands.concat(continuation.extraArgs)
                            currentIsWhnf = true
                        } else {
//                            deltaReductions += 1
//                            incrementCount(deltaCounts, continuation.primitiveConst.name)
                            currentExpression = definitionValue
                            currentLocals = ClosedEvalEnv.Empty
                            currentProjection = null
                            argumentStack = continuation.operands.concat(continuation.extraArgs)
                        }
                    } else {
                        currentExpression = reduced
                        currentLocals = ClosedEvalEnv.Empty
                        currentProjection = null
                        argumentStack = continuation.extraArgs
                    }
                }
            }
        }
    }
}

context(env: Environment)
private fun Expression.Const.closedNatPrimitive(): ClosedNatPrimitive? {
    val operationName = this.name as? Name.Str ?: return null
    val namespace = env.names[operationName.pre] as? Name.Str ?: return null
    if (namespace.pre != 0 || namespace.str != "Nat") return null
    if (this.levels.isNotEmpty()) return null
    return when (operationName.str) {
        "succ" -> ClosedNatPrimitive.Succ
        "add" -> ClosedNatPrimitive.Add
        "sub" -> ClosedNatPrimitive.Sub
        "mul" -> ClosedNatPrimitive.Mul
        "pow" -> ClosedNatPrimitive.Pow
        "div" -> ClosedNatPrimitive.Div
        "mod" -> ClosedNatPrimitive.Mod
        "beq" -> ClosedNatPrimitive.Beq
        "ble" -> ClosedNatPrimitive.Ble
        else -> null
    }
}

context(env: Environment)
private fun Expression.Proj.structuresHaveSameConstantHead(
    other: Expression.Proj,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val leftHead =
        this.structExpr.whnfCore(localCtxLeft, cheapProjection = true).asAppSpine().first as? Expression.Const
            ?: return false
    val rightHead =
        other.structExpr.whnfCore(localCtxRight, cheapProjection = true).asAppSpine().first as? Expression.Const
            ?: return false
    return leftHead.name == rightHead.name &&
            leftHead.levels.size == rightHead.levels.size &&
            leftHead.levels.indices.all { leftHead.levels[it].isEqual(rightHead.levels[it]) }
}

context(env: Environment)
private fun Expression.Proj.lazyProjectionDefEq(
    other: Expression.Proj,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    var left = this.structExpr.whnfCore(localCtxLeft, cheapProjection = true)
    var right = other.structExpr.whnfCore(localCtxRight, cheapProjection = true)
    while (true) {
        val quick = left.quickIsDefEq(right, localCtxLeft, localCtxRight)
        if (quick == true) return true
        left.tryRegularDefinitionCongruence(right, localCtxLeft, localCtxRight)?.let { return it }

        val leftStep = left.tryLazyDeltaStep()
        val rightStep = right.tryLazyDeltaStep()
        if (leftStep == null && rightStep == null || quick == false) {
            val leftField = this.reduceProjectionCore(left)
            val rightField = other.reduceProjectionCore(right)
            if (leftField != null && rightField != null) {
                return leftField.isDefEq(rightField, localCtxLeft, localCtxRight)
            }
            return left.isDefEq(right, localCtxLeft, localCtxRight)
        }
        if (leftStep != null && rightStep == null) {
            right.tryReduceProjectionForDelta(localCtxRight)?.let {
                right = it
                continue
            }
        } else if (leftStep == null && rightStep != null) {
            left.tryReduceProjectionForDelta(localCtxLeft)?.let {
                left = it
                continue
            }
        }
        when (chooseLazyDeltaSide(leftStep, rightStep)) {
            LazyDeltaChoice.Left -> left = leftStep!!.unfold(localCtxLeft)
            LazyDeltaChoice.Right -> right = rightStep!!.unfold(localCtxRight)
            LazyDeltaChoice.Both -> {
                left = leftStep!!.unfold(localCtxLeft)
                right = rightStep!!.unfold(localCtxRight)
            }

            null -> error("Lazy projection reduction had no available step")
        }
    }
}

context(env: Environment)
private fun Expression.defEqCacheKey(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): DefEqCacheKey {
    val leftCtxId = if (this.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxLeft)
    val rightCtxId = if (other.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxRight)
    return if (this.ie < other.ie || (this.ie == other.ie && leftCtxId <= rightCtxId)) {
        DefEqCacheKey(this.ie, other.ie, leftCtxId, rightCtxId)
    } else {
        DefEqCacheKey(other.ie, this.ie, rightCtxId, leftCtxId)
    }
}

context(env: Environment)
private fun Expression.tryKnownDefEqCongruence(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    if (this === other) return true
    val key = this.defEqCacheKey(other, localCtxLeft, localCtxRight)
    if (env.defEqEquivalences.areEquivalent(key)) return true

    val result = when (this) {
        is Expression.App -> other is Expression.App &&
                this.fnExpr.tryKnownDefEqCongruence(other.fnExpr, localCtxLeft, localCtxRight) &&
                this.argExpr.tryKnownDefEqCongruence(other.argExpr, localCtxLeft, localCtxRight)

        is Expression.Bvar -> other is Expression.Bvar && this.bvar == other.bvar
        is Expression.Const -> other is Expression.Const &&
                this.name == other.name &&
                this.levels.size == other.levels.size &&
                this.levels.indices.all { index -> this.levels[index].isEqual(other.levels[index]) }

        is Expression.Mdata -> other is Expression.Mdata &&
                this.expr.tryKnownDefEqCongruence(other.expr, localCtxLeft, localCtxRight)

        is Expression.NatVal -> other is Expression.NatVal && this.natVal == other.natVal
        is Expression.Proj -> other is Expression.Proj &&
                this.typeNameExpr == other.typeNameExpr &&
                this.projIndex == other.projIndex &&
                this.structExpr.tryKnownDefEqCongruence(other.structExpr, localCtxLeft, localCtxRight)

        is Expression.Sort -> other is Expression.Sort && this.level.isEqual(other.level)
        is Expression.StrVal -> other is Expression.StrVal && this.strVal == other.strVal
        is Expression.ForallE, is Expression.Lam, is Expression.LetE -> false
    }
    if (result) env.defEqEquivalences.addEquivalent(key)
    return result
}

context(env: Environment)
private fun Expression.isEagerReduceApp(): Boolean {
    val [head, arguments] = this.asAppSpine()
    val constant = head as? Expression.Const ?: return false
    val name = constant.name as? Name.Str ?: return false
    return name.pre == 0 && name.str == "eagerReduce" && arguments.size == 2
}

context(env: Environment)
private fun Expression.quickIsDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    if (this === other) return true
    this.tryNatOffsetDefEq(other, localCtxLeft, localCtxRight)?.let { return it }
    return when {
        this is Expression.Bvar && other is Expression.Bvar ->
            if (this.bvar == other.bvar) true else null
        this is Expression.ForallE && other is Expression.ForallE ->
            this.isDefEqBinding(other, localCtxLeft, localCtxRight, lambda = false)

        this is Expression.Lam && other is Expression.Lam ->
            this.isDefEqBinding(other, localCtxLeft, localCtxRight, lambda = true)

        this is Expression.Mdata && other is Expression.Mdata ->
            this.expr.isDefEq(other.expr, localCtxLeft, localCtxRight)

        this is Expression.NatVal && other is Expression.NatVal -> this.natVal == other.natVal
        this is Expression.Sort && other is Expression.Sort -> this.level.isEqual(other.level)
        this is Expression.StrVal && other is Expression.StrVal -> this.strVal == other.strVal
        else -> null
    }
}

context(env: Environment)
private fun Expression.unfoldValueOnce(): Expression? {
    val spine = this.asAppSpine()
    val constant = spine.first as? Expression.Const ?: return null
    return constant.instantiatedValue()?.applyArgs(spine.second)
}

context(env: Environment)
private fun Expression.Const.instantiatedValue(): Expression? {
    val value = when (val declaration = this.decl) {
        is Declaration.Def -> declaration.valueExpr
        is Declaration.Opaque -> declaration.valueExpr
        is Declaration.Thm -> declaration.valueExpr
        else -> return null
    }
    return env.unfoldedDefinitionCache.getOrPut(this.ie) {
        value.instantiateLevelParams(this.composeLevelSubst(emptyMap()))
    }
}

context(env: Environment)
private fun Expression.tryNatOffsetDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    var left = this
    var right = other
    var removedOffset = false
    while (true) {
        val leftLiteral = left.asNatLiteralValue()
        val rightLiteral = right.asNatLiteralValue()
        if (leftLiteral != null && rightLiteral != null) return leftLiteral == rightLiteral

        val leftPred = left.natPredecessorOrNull()
        val rightPred = right.natPredecessorOrNull()
        val leftZero = leftLiteral?.isZero() == true || left.isNatZeroCtorConst()
        val rightZero = rightLiteral?.isZero() == true || right.isNatZeroCtorConst()
        if ((leftZero && rightPred != null) || (rightZero && leftPred != null)) return false
        if (leftPred == null || rightPred == null) {
            return if (removedOffset) {
                val leftWhnf = if (leftPred == null) left.whnf(localCtx = localCtxLeft) else left
                val rightWhnf = if (rightPred == null) right.whnf(localCtx = localCtxRight) else right
                if (leftWhnf !== left || rightWhnf !== right) {
                    left = leftWhnf
                    right = rightWhnf
                    continue
                }
                left.isDefEq(right, localCtxLeft, localCtxRight)
            } else {
                null
            }
        }
        left = leftPred
        right = rightPred
        removedOffset = true
    }
}

context(env: Environment)
private fun Expression.natPredecessorOrNull(): Expression? {
    if (this is Expression.NatVal && !this.natVal.isZero()) {
        return env.addCustomExpr { Expression.NatVal(this.natVal.minus(1L), it) }
    }
    val app = this as? Expression.App ?: return null
    val spine = app.unfoldApp()
    val constant = spine.first as? Expression.Const ?: return null
    if (constant.levels.isNotEmpty() || constant.name.toStringDetailed() != "Nat.succ") return null
    return spine.second.singleOrNull()
}

private enum class LazyDeltaStepKind(val priority: Int) {
    Opaque(0),
    Regular(1),
    Abbrev(2),
}

private data class LazyDeltaStep(
    val expression: Expression,
    val kind: LazyDeltaStepKind,
    val regularHeight: Int = 0,
)

private data class LazyDeltaResult(
    val left: Expression,
    val right: Expression,
    val decision: Boolean? = null,
)

private enum class LazyDeltaChoice {
    Left,
    Right,
    Both,
}

internal data class NatLiteralRecursorRules(
    val zeroRule: Inductive.RecursorVal.RecursorRule,
    val succRule: Inductive.RecursorVal.RecursorRule,
)

context(env: Environment)
private fun Inductive.RecursorVal.natLiteralRecursorRules(): NatLiteralRecursorRules? {
    if (env.natLiteralRecursorRulesCache.containsKey(this.name)) {
        return env.natLiteralRecursorRulesCache[this.name]
    }
    val result = run {
        var zeroRule: Inductive.RecursorVal.RecursorRule? = null
        var succRule: Inductive.RecursorVal.RecursorRule? = null
        for (rule in this.rules) {
            val ctorDecl = env.constructorByName[rule.ctorName] ?: return@run null
            val inductiveName = ctorDecl.inductName as? Name.Str ?: return@run null
            if (
                inductiveName.pre != 0 || inductiveName.str != "Nat" ||
                ctorDecl.numParams != this.numParams || ctorDecl.numFields != rule.nfields
            ) return@run null
            when (ctorDecl.numFields) {
                0 -> if (zeroRule == null) zeroRule = rule else return@run null
                1 -> if (succRule == null) succRule = rule else return@run null
                else -> return@run null
            }
        }
        NatLiteralRecursorRules(zeroRule ?: return@run null, succRule ?: return@run null)
    }
    env.natLiteralRecursorRulesCache[this.name] = result
    return result
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
private fun Expression.lazyDeltaDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): LazyDeltaResult {
    var left = this
    var right = other
    var iterations = 0
    while (true) {
        iterations += 1
//        if (debugTargetDeclaration && iterations % 10_000 == 0) {
//            println(
//                "debug lazy progress: iterations=$iterations left=${left.debugHead()} " +
//                        "right=${right.debugHead()}"
//            )
//        }
        left.quickIsDefEq(right, localCtxLeft, localCtxRight)?.let {
            return LazyDeltaResult(left, right, it)
        }
        left.tryRegularDefinitionCongruence(right, localCtxLeft, localCtxRight)?.let {
            return LazyDeltaResult(left, right, it)
        }
        if (
            left.maxLooseBVarIndex() < 0 && right.maxLooseBVarIndex() < 0 ||
            env.eagerReduction
        ) {
            val reducedLeft = (left as? Expression.App)
                ?.tryReduceNatLiteral(emptyMap(), localCtxLeft, normalizeOperands = true)
            if (reducedLeft != null) {
                left = reducedLeft
                continue
            }
            val reducedRight = (right as? Expression.App)
                ?.tryReduceNatLiteral(emptyMap(), localCtxRight, normalizeOperands = true)
            if (reducedRight != null) {
                right = reducedRight
                continue
            }
            if (left.tryNatLiteralDefEq(right, localCtxLeft, localCtxRight)) {
                return LazyDeltaResult(left, right, true)
            }
        }
        val leftStep = left.tryLazyDeltaStep()
        val rightStep = right.tryLazyDeltaStep()
        if (leftStep == null && rightStep == null) {
            return LazyDeltaResult(left, right)
        }
        if (leftStep != null && rightStep == null) {
            right.tryReduceProjectionForDelta(localCtxRight)?.let {
                right = it
                continue
            }
            left = leftStep.unfold(localCtxLeft)
            continue
        } else if (leftStep == null && rightStep != null) {
            left.tryReduceProjectionForDelta(localCtxLeft)?.let {
                left = it
                continue
            }
            right = rightStep.unfold(localCtxRight)
            continue
        }
        val choice = chooseLazyDeltaSide(leftStep, rightStep)
        when (choice) {
            LazyDeltaChoice.Left -> left = leftStep!!.unfold(localCtxLeft)
            LazyDeltaChoice.Right -> right = rightStep!!.unfold(localCtxRight)
            LazyDeltaChoice.Both -> {
                left = leftStep!!.unfold(localCtxLeft)
                right = rightStep!!.unfold(localCtxRight)
            }

            null -> return LazyDeltaResult(left, right)
        }
    }
}

context(env: Environment)
private fun Expression.tryReduceProjectionForDelta(localCtx: List<Expression>): Expression? {
    val head = this.asAppSpine().first
    if (head !is Expression.Proj) return null
    return this.whnfCore(localCtx, cheapProjection = false).takeIf { it !== this }
}

context(env: Environment)
private fun Expression.App.isDefEqWhnfSpine(
    other: Expression.App,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
//    val traceSpine = debugTargetDeclaration &&
//            (this.ie == -3489 && other.ie == 2395 || this.ie == 2395 && other.ie == -3489)
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
    var functionType: Expression.ForallE? = null
    var pendingSubst = emptyList<Expression>()

    fun advanceFunctionType(type: Expression.ForallE, argument: Expression): Expression.ForallE {
        pendingSubst = listOf(argument) + pendingSubst
        val directForall = type.bodyExpr as? Expression.ForallE
        if (directForall != null) return directForall
        val nextType = type.bodyExpr.applySubst(pendingSubst)
        pendingSubst = emptyList()
        return nextType.whnf(localCtx = localCtxLeft) as? Expression.ForallE
            ?: error("Application spine has more arguments than its function type")
    }

    for (index in leftArgs.indices) {
        val leftArgument = leftArgs[index]
        val rightArgument = rightArgs[index]
//        if (traceSpine) {
//            println(
//                "debug spine argument: index=$index left=${leftArgument.debugShallow()} " +
//                        "right=${rightArgument.debugShallow()}"
//            )
//        }
        if (leftArgument !== rightArgument) {
//            if (
//                debugTargetDeclaration &&
//                (leftArgument.debugContainsConstant("Nat.decLe") || rightArgument.debugContainsConstant("Nat.decLe"))
//            ) {
//                println(
//                    "debug Nat.decLe congruence: index=$index left=${leftArgument.debugHead()} " +
//                            "right=${rightArgument.debugHead()}"
//                )
//            }
            if (functionType == null) {
                functionType = leftSpine.first.inferType(localCtx = localCtxLeft, validate = false)
                    .whnf(localCtx = localCtxLeft) as? Expression.ForallE
                    ?: error("Application head does not have a function type")
                for (priorIndex in 0 until index) {
                    functionType = advanceFunctionType(functionType!!, leftArgs[priorIndex])
                }
            }
            val domain = functionType.typeExpr.applySubst(pendingSubst)
            val domainIsProp = domain
                .inferSort(localCtx = localCtxLeft, validate = false)
                .isLessOrEqual(Level.Zero)
            if (domainIsProp) {
                env.typedCongruenceProofSkips += 1
            } else if (!leftArgument.isDefEq(rightArgument, localCtxLeft, localCtxRight)) {
//                if (debugTargetDeclaration) {
//                    println(
//                        "debug congruence failure: index=$index " +
//                                "leftId=${leftArgument.ie} rightId=${rightArgument.ie} " +
//                                "left=${leftArgument.debugShallow()} right=${rightArgument.debugShallow()}"
//                    )
//                }
                return false
            }
        }
        if (functionType != null && index < leftArgs.lastIndex) {
            functionType = advanceFunctionType(functionType, leftArgument)
        }
    }
    return true
}

context(env: Environment)
private fun Expression.tryStructuralDefEq(other: Expression): Boolean? {
    val pending = ArrayDeque<Pair<Expression, Expression>>()
    val visited = mutableSetOf<ExprPairKey>()
    pending.addLast(this to other)
    while (pending.isNotEmpty()) {
        val [left, right] = pending.removeLast()
        if (left === right) continue
        if (!visited.add(ExprPairKey(left.ie, right.ie))) continue

        when {
            left is Expression.Mdata -> pending.addLast(left.expr to right)
            right is Expression.Mdata -> pending.addLast(left to right.expr)
            left is Expression.App && right is Expression.App -> {
                pending.addLast(left.fnExpr to right.fnExpr)
                pending.addLast(left.argExpr to right.argExpr)
            }

            left is Expression.ForallE && right is Expression.ForallE -> {
                pending.addLast(left.typeExpr to right.typeExpr)
                pending.addLast(left.bodyExpr to right.bodyExpr)
            }

            left is Expression.Lam && right is Expression.Lam -> {
                pending.addLast(left.typeExpr to right.typeExpr)
                pending.addLast(left.bodyExpr to right.bodyExpr)
            }

            left is Expression.LetE && right is Expression.LetE -> {
                pending.addLast(left.typeExpr to right.typeExpr)
                pending.addLast(left.valueExpr to right.valueExpr)
                pending.addLast(left.bodyExpr to right.bodyExpr)
            }

            left is Expression.Proj && right is Expression.Proj -> {
                if (left.typeNameIndex != right.typeNameIndex || left.projIndex != right.projIndex) return null
                pending.addLast(left.structExpr to right.structExpr)
            }

            left is Expression.Bvar && right is Expression.Bvar -> {
                if (left.bvar != right.bvar) return null
            }

            left is Expression.Const && right is Expression.Const -> {
                if (
                    left.name != right.name ||
                    left.levels.size != right.levels.size ||
                    !left.levels.indices.all { left.levels[it].isEqual(right.levels[it]) }
                ) return null
            }

            left is Expression.NatVal && right is Expression.NatVal -> if (left.natVal != right.natVal) return null
            left is Expression.Sort && right is Expression.Sort -> if (!left.level.isEqual(right.level)) return null
            left is Expression.StrVal && right is Expression.StrVal -> if (left.strVal != right.strVal) return null
            else -> return null
        }
    }
    return true
}

context(env: Environment)
private fun Expression.tryConstantApplicationCongruence(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftApp = this as? Expression.App ?: return null
    val rightApp = other as? Expression.App ?: return null
    val leftSpine = leftApp.unfoldApp()
    val rightSpine = rightApp.unfoldApp()
    val leftHead = leftSpine.first as? Expression.Const ?: return null
    val rightHead = rightSpine.first as? Expression.Const ?: return null
    if (
        leftHead.name != rightHead.name ||
        leftHead.levels.size != rightHead.levels.size ||
        !leftHead.levels.indices.all { leftHead.levels[it].isEqual(rightHead.levels[it]) } ||
        leftSpine.second.size != rightSpine.second.size
    ) return null
    return leftApp.isDefEqWhnfSpine(rightApp, localCtxLeft, localCtxRight)
}

context(env: Environment)
private fun Expression.tryRegularDefinitionCongruence(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean? {
    val leftApp = this as? Expression.App ?: return null
    val rightApp = other as? Expression.App ?: return null
    val leftSpine = leftApp.unfoldApp()
    val rightSpine = rightApp.unfoldApp()
    val leftHead = leftSpine.first as? Expression.Const ?: return null
    val rightHead = rightSpine.first as? Expression.Const ?: return null
    val leftHints = (leftHead.decl as? Declaration.Def)?.hints as? Declaration.Def.Hints.Regular ?: return null
    val rightHints = (rightHead.decl as? Declaration.Def)?.hints as? Declaration.Def.Hints.Regular ?: return null
    if (
        leftHead.name != rightHead.name ||
        leftHints.value != rightHints.value ||
        leftHead.levels.size != rightHead.levels.size ||
        !leftHead.levels.indices.all { leftHead.levels[it].isEqual(rightHead.levels[it]) }
    ) return null

    val failureKey = this.defEqCacheKey(other, localCtxLeft, localCtxRight)
    if (failureKey in env.defEqAppFailures) return null
    if (leftApp.tryConstantApplicationCongruence(rightApp, localCtxLeft, localCtxRight) == true) {
        return true
    }
    env.defEqAppFailures += failureKey
    return null
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
private fun Expression.tryLazyDeltaStep(): LazyDeltaStep? {
    val spine = this.asAppSpine()
    val headExpr = spine.first
    // A projection is not itself a delta target. Keeping it out of the ordinary
    // hint comparison lets the projection-specific paths reduce its structure first.
    if (headExpr is Expression.Proj) return null
    val projectionInfo = (headExpr as? Expression.Const)?.projectionReductionInfo()
    if (projectionInfo != null && spine.second.size < projectionInfo.arity) return null
    val headStep = headExpr.lazyDeltaStepInfo() ?: return null
    return LazyDeltaStep(
        expression = this,
        kind = headStep.kind,
        regularHeight = headStep.regularHeight,
    )
}

context(env: Environment)
private fun LazyDeltaStep.unfold(localCtx: List<Expression>): Expression {
    val spine = expression.asAppSpine()
    val projectionHead = spine.first as? Expression.Proj
    val unfolded = if (projectionHead != null) {
        val structStep = projectionHead.structExpr.tryLazyDeltaStep()
            ?: error("Selected projection delta step could not unfold its structure")
        val unfoldedStruct = structStep.unfold(localCtx)
        val projection = env.addCustomExpr {
            projectionHead.copy(struct = unfoldedStruct.ie, ie = it)
        } as Expression.Proj
        projection.reduceProjectionCore(unfoldedStruct)?.applyArgs(spine.second)
            ?: projection.applyArgs(spine.second)
    } else {
        val projection = (expression as? Expression.App)?.tryReduceProjectionApp()
        projection ?: run {
            val head = spine.first as? Expression.Const
                ?: error("Selected lazy delta step has no constant head")
            head.instantiatedValue()?.applyBetaArgs(spine.second)
                ?: error("Selected lazy delta step could not unfold")
        }
    }
    val normalized = unfolded
        .reduceBetaLetHead()
        .whnfCore(localCtx, cheapProjection = true)
    check(normalized !== expression) { "Selected lazy delta step made no progress" }
    return normalized
}

context(env: Environment)
private fun Expression.reduceBetaLetHead(): Expression {
    var current = this
    while (true) {
        current = when (current) {
            is Expression.Mdata -> current.expr
            is Expression.LetE -> current.bodyExpr.applySubst(listOf(current.valueExpr))
            is Expression.App -> {
                val spine = current.unfoldApp()
                when (val head = spine.first) {
                    is Expression.Mdata -> head.expr.applyArgs(spine.second)
                    is Expression.LetE ->
                        head.bodyExpr.applySubst(listOf(head.valueExpr)).applyArgs(spine.second)

                    is Expression.Lam -> head.applyBetaArgs(spine.second)
                    else -> return current
                }
            }

            else -> return current
        }
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
private fun Expression.applyBetaArgs(args: List<Expression>): Expression {
    var head = this
    var nextArg = 0
    while (true) {
        when (head) {
            is Expression.Mdata -> head = head.expr
            is Expression.LetE -> head = head.bodyExpr.applySubst(listOf(head.valueExpr))
            is Expression.Lam -> {
                if (nextArg == args.size) return head
                var body: Expression = head
                var consumedArgs = 0
                while (body is Expression.Lam && nextArg + consumedArgs < args.size) {
                    body = body.bodyExpr
                    consumedArgs += 1
                }
                head = body.applySubst(args.subList(nextArg, nextArg + consumedArgs).asReversed())
                nextArg += consumedArgs
            }

            else -> return head.applyArgs(args.drop(nextArg))
        }
    }
}

private data class LazyDeltaHeadInfo(
    val kind: LazyDeltaStepKind,
    val regularHeight: Int = 0,
)

context(env: Environment)
private fun Expression.lazyDeltaStepInfo(): LazyDeltaHeadInfo? = when (this) {
    is Expression.Const -> {
        when (val declaration = this.decl) {
            is Declaration.Def -> when (val hints = declaration.hints) {
                Declaration.Def.Hints.Opaque -> LazyDeltaHeadInfo(LazyDeltaStepKind.Opaque)
                Declaration.Def.Hints.Abbrev -> LazyDeltaHeadInfo(LazyDeltaStepKind.Abbrev)
                is Declaration.Def.Hints.Regular -> LazyDeltaHeadInfo(LazyDeltaStepKind.Regular, hints.value)
            }

            is Declaration.Opaque, is Declaration.Thm -> LazyDeltaHeadInfo(LazyDeltaStepKind.Opaque)
            else -> null
        }
    }

    else -> null
}

context(env: Environment)
fun Expression.asAppSpine(): Pair<Expression, List<Expression>> = when (this) {
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
            this.isDefEqBinding(other, localCtxLeft, localCtxRight, lambda = false)
        }

        is Expression.Lam if other is Expression.Lam -> {
            this.isDefEqBinding(other, localCtxLeft, localCtxRight, lambda = true)
        }

        is Expression.Lam ->
            this.tryCompareWithFunction(other, localCtxLeft, localCtxRight) ?: false

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
        else -> if (other is Expression.Lam) {
            this.tryCompareWithFunction(other, localCtxLeft, localCtxRight) ?: false
        } else {
            false
        }
    }
    if (result) return true
    val leftIsConstructor = (this.asAppSpine().first as? Expression.Const)?.decl is Inductive.ConstructorVal
    val rightIsConstructor = (other.asAppSpine().first as? Expression.Const)?.decl is Inductive.ConstructorVal
    // Constructor applications are already canonical: typed congruence above decides them.
    // Eta is needed only to compare a constructor with a neutral structure value.
    if (leftIsConstructor && rightIsConstructor) return false
    return this.canBeStructureLikeValue() &&
            other.canBeStructureLikeValue() &&
            this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight)
}

context(env: Environment)
private fun Expression.isDefEqBinding(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
    lambda: Boolean,
): Boolean {
    var left = this
    var right = other
    var leftCtx = localCtxLeft
    var rightCtx = localCtxRight
    while (true) {
        val leftDomain = if (lambda) {
            (left as? Expression.Lam)?.typeExpr
        } else {
            (left as? Expression.ForallE)?.typeExpr
        } ?: break
        val rightDomain = if (lambda) {
            (right as? Expression.Lam)?.typeExpr
        } else {
            (right as? Expression.ForallE)?.typeExpr
        } ?: break
        if (leftDomain !== rightDomain && !leftDomain.isDefEq(rightDomain, leftCtx, rightCtx)) return false

        left = if (lambda) (left as Expression.Lam).bodyExpr else (left as Expression.ForallE).bodyExpr
        right = if (lambda) (right as Expression.Lam).bodyExpr else (right as Expression.ForallE).bodyExpr
        leftCtx = env.consLocalCtx(leftDomain, leftCtx)
        rightCtx = env.consLocalCtx(rightDomain, rightCtx)
    }
    return left.isDefEq(right, leftCtx, rightCtx)
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
        (this.inferType(localCtx = localCtxLeft, validate = false)
            .whnf(localCtx = localCtxLeft) as? Expression.ForallE)?.typeExpr
            ?: return null
    }
    val rightDomain = if (rightLam != null) {
        rightLam.typeExpr
    } else {
        (other.inferType(localCtx = localCtxRight, validate = false)
            .whnf(localCtx = localCtxRight) as? Expression.ForallE)?.typeExpr
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

private sealed interface InferredTypeResult {
    data class Syntax(val expression: Expression) : InferredTypeResult
    data class Semantic(val closure: ClosedClosure) : InferredTypeResult
}

private sealed interface InferFrame {
    data class Cache(val key: InferTypeCacheKey) : InferFrame
    data class AppFunction(
        val expression: Expression.App,
        val args: List<Expression>,
        val validate: Boolean,
        val localCtx: List<Expression>,
    ) : InferFrame
    data class AppArgument(
        val expression: Expression.App,
        val args: List<Expression>,
        val index: Int,
        val functionType: ClosedValue,
        val expectedType: ClosedClosure,
        val argument: Expression,
        val localCtx: List<Expression>,
    ) : InferFrame

    data class ExpectedType(
        val expectedBodyType: ClosedClosure,
        val resultType: ClosedClosure,
        val bodyCtx: List<Expression>,
        val subject: Expression,
    ) : InferFrame
    data class OpenPi(val expression: Expression.ForallE, val domainCtx: List<Expression>)
    data class PiDomains(
        val opened: List<OpenPi>,
        val tail: Expression,
        val tailCtx: List<Expression>,
        val index: Int,
        val domainSorts: List<Level>,
    ) : InferFrame

    data class PiBody(val domainSorts: List<Level>, val tail: Expression, val tailCtx: List<Expression>) : InferFrame
    data class OpenLambda(val expression: Expression.Lam, val domainCtx: List<Expression>)
    data class LambdaDomains(
        val opened: List<OpenLambda>,
        val tail: Expression,
        val tailCtx: List<Expression>,
        val index: Int,
    ) : InferFrame

    data class LambdaBody(
        val opened: List<OpenLambda>,
        val bodyCtx: List<Expression>,
    ) : InferFrame
    data class LetType(
        val expression: Expression.LetE,
        val localCtx: List<Expression>,
    ) : InferFrame
    data class LetValue(
        val expression: Expression.LetE,
        val localCtx: List<Expression>,
    ) : InferFrame
    data class LetBody(
        val value: Expression,
        val bodyCtx: List<Expression>,
    ) : InferFrame
    data class Projection(
        val expression: Expression.Proj,
        val localCtx: List<Expression>,
    ) : InferFrame
}

@IgnorableReturnValue
context(env: Environment)
private fun requireSort(type: Expression, subject: Expression, localCtx: List<Expression>): Level {
    val typeWhnf = type.whnf(localCtx = localCtx)
    val sort = typeWhnf as? Expression.Sort
        ?: error("Expected Sort type for ${subject.toStringDetailed()}, got ${typeWhnf.toStringDetailed()}")
    return sort.level
}

context(env: Environment)
private fun Expression.inferTypeCore(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
    validate: Boolean = true,
): InferredTypeResult {
    val expression = this.instantiateLevelParams(levelSubst)
    check(expression.hasNoUnboundBvars(localCtx.size)) {
        "Inference received an expression outside its context: ${expression.toStringDetailed()}"
    }
    val frames = ArrayDeque<InferFrame>()
    var current = expression
    var currentCtx = localCtx
    var result: Expression = expression
    var semanticResult: ClosedClosure? = null
    var evaluating = true

    fun materializeResult(resultCtx: List<Expression>): Expression {
        semanticResult?.let { semantic ->
            result = semantic.reify(resultCtx.closedEvalEnv())
            semanticResult = null
        }
        return result
    }

    fun requireSortResult(subject: Expression, resultCtx: List<Expression>): Level {
        semanticResult?.trySemanticWhnf()?.let { value ->
            val sort = value.head.expression as? Expression.Sort
            if (sort != null && value.arguments.isEmpty()) {
                semanticResult = null
                return sort.level
            }
        }
        return requireSort(materializeResult(resultCtx), subject, resultCtx)
    }

    while (true) {
        if (evaluating) {
            semanticResult = null
            val contextId = if (current.maxLooseBVarIndex() < 0) 0 else env.localCtxId(currentCtx)
            val cacheKey = InferTypeCacheKey(current.ie, contextId, validate)
            val cachedSemanticType = env.semanticRuntime.inferredTypes[cacheKey]
                ?: if (validate) null else env.semanticRuntime.inferredTypes[cacheKey.copy(validate = true)]
            cachedSemanticType?.let {
                env.inferTypeCacheHits += 1
                semanticResult = it
                evaluating = false
                continue
            }
            val cachedType = env.inferTypeCacheNoLevelSubst[cacheKey]
                ?: if (validate) null else env.inferTypeCacheNoLevelSubst[cacheKey.copy(validate = true)]
            cachedType?.let {
                env.inferTypeCacheHits += 1
                result = it
                evaluating = false
                continue
            }
            frames.addLast(InferFrame.Cache(cacheKey))
            when (val expr = current) {
                is Expression.App -> {
                    val [head, args] = expr.unfoldApp()
                    frames.addLast(InferFrame.AppFunction(expr, args, validate, currentCtx))
                    current = head
                }

                is Expression.Bvar -> {
                    check(expr.bvar in currentCtx.indices) { "Unbound bvar ${expr.bvar} in ${expr.toStringDetailed()}" }
                    result = currentCtx[expr.bvar].lift(expr.bvar + 1)
                    evaluating = false
                }

                is Expression.Const -> {
                    val type = env.declTypeByName[expr.name] ?: error("Declaration not found for ${expr.name}")
                    result = type.instantiateLevelParams(expr.composeLevelSubst(emptyMap()))
                    evaluating = false
                }

                is Expression.ForallE -> {
                    val opened = mutableListOf<InferFrame.OpenPi>()
                    var binder: Expression = expr
                    var binderCtx = currentCtx
                    while (binder is Expression.ForallE) {
                        opened += InferFrame.OpenPi(binder, binderCtx)
                        binderCtx = env.consLocalCtx(binder.typeExpr, binderCtx)
                        binder = binder.bodyExpr
                    }
                    frames.addLast(InferFrame.PiDomains(opened, binder, binderCtx, 0, emptyList()))
                    current = opened.first().expression.typeExpr
                    currentCtx = opened.first().domainCtx
                }

                is Expression.Lam -> {
                    val opened = mutableListOf<InferFrame.OpenLambda>()
                    var binder: Expression = expr
                    var binderCtx = currentCtx
                    while (binder is Expression.Lam) {
                        opened += InferFrame.OpenLambda(binder, binderCtx)
                        binderCtx = env.consLocalCtx(binder.typeExpr, binderCtx)
                        binder = binder.bodyExpr
                    }
                    if (validate) {
                        frames.addLast(InferFrame.LambdaDomains(opened, binder, binderCtx, 0))
                        current = opened.first().expression.typeExpr
                        currentCtx = opened.first().domainCtx
                    } else {
                        frames.addLast(InferFrame.LambdaBody(opened, binderCtx))
                        current = binder
                        currentCtx = binderCtx
                    }
                }

                is Expression.Sort -> {
                    val newLevel = env.addCustomSuccLevel(expr.level.il)
                    result = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
                    evaluating = false
                }

                is Expression.LetE -> {
                    if (validate) {
                        frames.addLast(InferFrame.LetType(expr, currentCtx))
                        current = expr.typeExpr
                    } else {
                        frames.addLast(
                            InferFrame.LetBody(
                                expr.valueExpr,
                                env.consLocalCtx(expr.typeExpr, currentCtx, expr.valueExpr),
                            )
                        )
                        current = expr.bodyExpr
                        currentCtx = env.consLocalCtx(expr.typeExpr, currentCtx, expr.valueExpr)
                    }
                }

                is Expression.Mdata -> current = expr.expr
                is Expression.NatVal -> {
                    val natTypeIndex = env.findRootInductive("Nat")?.first
                        ?: error("Nat literal ${expr.natVal} used without Nat inductive in environment")
                    result = env.addCustomExpr { Expression.Const(_name = natTypeIndex, us = emptyList(), ie = it) }
                    evaluating = false
                }

                is Expression.Proj -> {
                    frames.addLast(InferFrame.Projection(expr, currentCtx))
                    current = expr.structExpr
                }

                is Expression.StrVal -> {
                    val stringTypeIndex = env.findRootInductive("String")?.first
                        ?: error("String literal used without String inductive in environment")
                    result = env.addCustomExpr { Expression.Const(_name = stringTypeIndex, us = emptyList(), ie = it) }
                    evaluating = false
                }
            }
            continue
        }

        if (frames.isEmpty()) {
            return semanticResult?.let(InferredTypeResult::Semantic)
                ?: InferredTypeResult.Syntax(result)
        }
        when (val frame = frames.removeLast()) {
            is InferFrame.Cache -> {
                val semantic = semanticResult
                if (semantic == null) {
                    env.inferTypeCacheNoLevelSubst[frame.key] = result
                } else {
                    env.semanticRuntime.inferredTypes[frame.key] = semantic
                }
            }
            is InferFrame.AppFunction -> {
                val baseLocals = frame.localCtx.closedEvalEnv()
                var functionType = (semanticResult ?: ClosedClosure(result, baseLocals)).inferFunctionType(
                    baseLocals,
                    frame.localCtx,
                    frame.expression,
                )
                if (frame.validate) {
                    val argument = frame.args.first()
                    val pi = functionType.head.expression as Expression.ForallE
                    val expectedType = ClosedClosure(pi.typeExpr, functionType.head.locals)
                    frames.addLast(
                        InferFrame.AppArgument(
                            frame.expression,
                            frame.args,
                            0,
                            functionType,
                            expectedType,
                            argument,
                            frame.localCtx,
                        )
                    )
                    val lambdaPlan = argument.openLambdasAgainst(expectedType, frame.localCtx)
                    if (!lambdaPlan.opened) {
                        current = argument
                        currentCtx = frame.localCtx
                        evaluating = true
                    } else {
                        check(lambdaPlan.valid) {
                            "Application argument type mismatch in app ${frame.expression.toStringDetailed()}"
                        }
                        frames.addLast(
                            InferFrame.ExpectedType(
                                lambdaPlan.expectedType,
                                expectedType,
                                lambdaPlan.localCtx,
                                frame.expression,
                            )
                        )
                        current = lambdaPlan.body
                        currentCtx = lambdaPlan.localCtx
                        evaluating = true
                    }
                } else {
                    frame.args.forEachIndexed { index, argument ->
                        val pi = functionType.head.expression as Expression.ForallE
                        val argumentClosure = ClosedClosure(argument, baseLocals).also {
                            it.semanticType = ClosedClosure(pi.typeExpr, functionType.head.locals)
                        }
                        val body = ClosedClosure(
                            pi.bodyExpr,
                            ClosedEvalEnv.Bind(
                                argumentClosure,
                                functionType.head.locals,
                            ),
                        )
                        if (index == frame.args.lastIndex) {
                            semanticResult = body
                        } else {
                            functionType = body.inferFunctionType(
                                baseLocals,
                                frame.localCtx,
                                frame.expression,
                            )
                        }
                    }
                }
            }

            is InferFrame.AppArgument -> {
//                if (debugTargetDeclaration) {
//                    println(
//                        "debug argument type: expected=${frame.expectedType.debugHead()} " +
//                                "inferred=${result.debugHead()} argument=${frame.argument.debugHead()}"
//                    )
//                }
//                if (
//                    debugTargetDeclaration &&
//                    (frame.expectedType.debugContainsConstant("Nat.decLe") || result.debugContainsConstant("Nat.decLe"))
//                ) {
//                    println(
//                        "debug Nat.decLe argument type: expected=${frame.expectedType.debugHead()} " +
//                                "inferred=${result.debugHead()} argument=${frame.argument.debugHead()}"
//                    )
//                }
                val previousEagerReduction = env.eagerReduction
                if (frame.argument.isEagerReduceApp()) env.eagerReduction = true
                val baseLocals = frame.localCtx.closedEvalEnv()
                val inferredType = semanticResult ?: ClosedClosure(result, baseLocals)
                val argumentTypeMatches = try {
                    val semanticMatch = frame.expectedType.trySemanticDefEq(inferredType)
                    if (semanticMatch) {
                        true
                    } else {
                        val expectedSyntax = frame.expectedType.reify(baseLocals)
                        val inferredSyntax = inferredType.reify(baseLocals)
                        expectedSyntax.isDefEqWithoutSemantic(
                            inferredSyntax,
                            frame.localCtx,
                            frame.localCtx,
                        )
                    }
                } finally {
                    env.eagerReduction = previousEagerReduction
                }
//                if (debugTargetDeclaration && !argumentTypeMatches) {
//                    println(
//                        "debug mismatch shape: expected=${frame.expectedType.debugShallow()} " +
//                                "inferred=${result.debugShallow()} argument=${frame.argument.debugShallow()}"
//                    )
//                    println("debug application shape: ${frame.expression.debugShallow()}")
//                    val pendingConstants = ArrayDeque<Expression>()
//                    val seenConstants = mutableSetOf<Int>()
//                    pendingConstants.addLast(result)
//                    while (pendingConstants.isNotEmpty()) {
//                        val expression = pendingConstants.removeLast()
//                        if (!seenConstants.add(expression.ie)) continue
//                        when (expression) {
//                            is Expression.App -> {
//                                pendingConstants.addLast(expression.fnExpr)
//                                pendingConstants.addLast(expression.argExpr)
//                            }
//                            is Expression.Const -> if (
//                                expression.name.toStringDetailed() == "AbsoluteValue.IsAdmissible.card"
//                            ) {
//                                println(
//                                    "debug card type=${expression.inferType(validate = false).debugShallow()} " +
//                                            "value=${expression.instantiatedValue()?.debugShallow()}"
//                                )
//                                var cardBody = expression.instantiatedValue()
//                                val cardDomains = mutableListOf<String>()
//                                while (cardBody is Expression.Lam) {
//                                    cardDomains += cardBody.typeExpr.debugShallow()
//                                    cardBody = cardBody.bodyExpr
//                                }
//                                println(
//                                    "debug card body: binders=${cardDomains.size} " +
//                                            "domains=${cardDomains.joinToString()} tail=${cardBody?.debugShallow()}"
//                                )
//                            }
//                            is Expression.ForallE -> {
//                                pendingConstants.addLast(expression.typeExpr)
//                                pendingConstants.addLast(expression.bodyExpr)
//                            }
//                            is Expression.Lam -> {
//                                pendingConstants.addLast(expression.typeExpr)
//                                pendingConstants.addLast(expression.bodyExpr)
//                            }
//                            is Expression.LetE -> {
//                                pendingConstants.addLast(expression.typeExpr)
//                                pendingConstants.addLast(expression.valueExpr)
//                                pendingConstants.addLast(expression.bodyExpr)
//                            }
//                            is Expression.Mdata -> pendingConstants.addLast(expression.expr)
//                            is Expression.Proj -> pendingConstants.addLast(expression.structExpr)
//                            is Expression.Bvar, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> {}
//                        }
//                    }
//                    println(
//                        "debug context values: " + frame.localCtx.indices
//                            .filter { env.localCtxValue(frame.localCtx, it) != null }
//                            .joinToString { index ->
//                                "$index=${env.localCtxValue(frame.localCtx, index)!!.debugShallow()}"
//                            }
//                    )
//                }
                check(argumentTypeMatches) {
                    "Application argument type mismatch in app ${frame.expression.toStringDetailed()}: " +
                            "expected ${frame.expectedType.reify(baseLocals).toStringDetailed()}, " +
                            "got ${inferredType.reify(baseLocals).toStringDetailed()}"
                }
                val functionPi = frame.functionType.head.expression as Expression.ForallE
                val argumentClosure = ClosedClosure(frame.argument, baseLocals).also {
                    it.semanticType = frame.expectedType
                }
                val body = ClosedClosure(
                    functionPi.bodyExpr,
                    ClosedEvalEnv.Bind(
                        argumentClosure,
                        frame.functionType.head.locals,
                    ),
                )
                val nextIndex = frame.index + 1
                if (nextIndex == frame.args.size) {
                    semanticResult = body
                } else {
                    val functionType = body.inferFunctionType(
                        baseLocals,
                        frame.localCtx,
                        frame.expression,
                    )
                    val nextPi = functionType.head.expression as Expression.ForallE
                    val expectedType = ClosedClosure(nextPi.typeExpr, functionType.head.locals)
                    val argument = frame.args[nextIndex]
                    frames.addLast(
                        InferFrame.AppArgument(
                            frame.expression,
                            frame.args,
                            nextIndex,
                            functionType,
                            expectedType,
                            argument,
                            frame.localCtx,
                        )
                    )
                    val lambdaPlan = argument.openLambdasAgainst(expectedType, frame.localCtx)
                    if (!lambdaPlan.opened) {
                        current = argument
                        currentCtx = frame.localCtx
                        evaluating = true
                    } else {
                        check(lambdaPlan.valid) {
                            "Application argument type mismatch in app ${frame.expression.toStringDetailed()}"
                        }
                        frames.addLast(
                            InferFrame.ExpectedType(
                                lambdaPlan.expectedType,
                                expectedType,
                                lambdaPlan.localCtx,
                                frame.expression,
                            )
                        )
                        current = lambdaPlan.body
                        currentCtx = lambdaPlan.localCtx
                        evaluating = true
                    }
                }
            }

            is InferFrame.ExpectedType -> {
                val inferred = semanticResult?.let(InferredTypeResult::Semantic)
                    ?: InferredTypeResult.Syntax(result)
                check(inferred.matchesExpectedType(frame.expectedBodyType, frame.bodyCtx)) {
                    "Application argument type mismatch in app ${frame.subject.toStringDetailed()}"
                }
                semanticResult = frame.resultType
            }

            is InferFrame.PiDomains -> {
                val opened = frame.opened[frame.index]
                val domainSorts = frame.domainSorts +
                        requireSortResult(opened.expression.typeExpr, opened.domainCtx)
                val nextIndex = frame.index + 1
                if (nextIndex < frame.opened.size) {
                    frames.addLast(frame.copy(index = nextIndex, domainSorts = domainSorts))
                    current = frame.opened[nextIndex].expression.typeExpr
                    currentCtx = frame.opened[nextIndex].domainCtx
                } else {
                    frames.addLast(InferFrame.PiBody(domainSorts, frame.tail, frame.tailCtx))
                    current = frame.tail
                    currentCtx = frame.tailCtx
                }
                evaluating = true
            }

            is InferFrame.PiBody -> {
                var level = requireSortResult(frame.tail, frame.tailCtx)
                for (domainSort in frame.domainSorts.asReversed()) {
                    level = makeLevelImax(domainSort, level)
                }
                result = env.addCustomExpr { Expression.Sort(level.il, it) }
            }

            is InferFrame.LambdaDomains -> {
                val opened = frame.opened[frame.index]
                requireSortResult(opened.expression.typeExpr, opened.domainCtx)
                val nextIndex = frame.index + 1
                if (nextIndex < frame.opened.size) {
                    frames.addLast(frame.copy(index = nextIndex))
                    current = frame.opened[nextIndex].expression.typeExpr
                    currentCtx = frame.opened[nextIndex].domainCtx
                } else {
                    frames.addLast(InferFrame.LambdaBody(frame.opened, frame.tailCtx))
                    current = frame.tail
                    currentCtx = frame.tailCtx
                }
                evaluating = true
            }

            is InferFrame.LambdaBody -> {
                result = materializeResult(frame.bodyCtx)
                for (opened in frame.opened.asReversed()) {
                    result = env.addCustomExpr {
                        opened.expression.copyAsForAllE().copy(body = result.ie, ie = it)
                    }
                }
            }

            is InferFrame.LetType -> {
                requireSortResult(frame.expression.typeExpr, frame.localCtx)
                frames.addLast(
                    InferFrame.LetValue(
                        frame.expression,
                        frame.localCtx,
                    )
                )
                current = frame.expression.valueExpr
                currentCtx = frame.localCtx
                evaluating = true
            }

            is InferFrame.LetValue -> {
                val expression = frame.expression
                val valueType = materializeResult(frame.localCtx)
                check(expression.typeExpr.isDefEq(valueType, frame.localCtx, frame.localCtx)) {
                    "Let value type mismatch in ${frame.expression.toStringDetailed()}: " +
                            "expected ${expression.typeExpr.toStringDetailed()}, got ${valueType.toStringDetailed()}"
                }
                frames.addLast(
                    InferFrame.LetBody(
                        expression.valueExpr,
                        env.consLocalCtx(expression.typeExpr, frame.localCtx, expression.valueExpr),
                    )
                )
                current = expression.bodyExpr
                currentCtx = env.consLocalCtx(expression.typeExpr, frame.localCtx, expression.valueExpr)
                evaluating = true
            }

            is InferFrame.LetBody ->
                result = materializeResult(frame.bodyCtx).applySubst(listOf(frame.value))

            is InferFrame.Projection ->
                result = frame.expression.inferProjectionType(
                    materializeResult(frame.localCtx),
                    frame.localCtx,
                )
        }
    }
}

context(env: Environment)
fun Expression.inferType(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
    validate: Boolean = true,
): Expression = when (val inferred = inferTypeCore(levelSubst, localCtx, validate)) {
    is InferredTypeResult.Syntax -> inferred.expression
    is InferredTypeResult.Semantic -> inferred.closure.reify(localCtx.closedEvalEnv())
}

context(env: Environment)
fun Expression.whnf(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
): Expression {
    val instantiated = if (levelSubst.isEmpty()) this else this.instantiateLevelParams(levelSubst)
    if (instantiated.isWhnfByShape() &&
        (instantiated !is Expression.Bvar || env.localCtxValue(localCtx, instantiated.bvar) == null)
    ) return instantiated
    return instantiated.normalizeWhnf(localCtx, WhnfMode.Full)
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
                    is Expression.Bvar -> {
                        val value = env.localCtxValue(localCtx, current.bvar)
                        if (value == null) result = current else current = value.lift(current.bvar + 1)
                    }
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
                    val unfolded = if (result.isNatLiteralPrimitive()) null else result.unfoldValueOnce()
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
                    val unfolded = frame.app.unfoldValueOnce()
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
                            val unfolded = frame.app.unfoldValueOnce()
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
                    head = head.bodyExpr
                    consumedArgs += 1
                }
                if (consumedArgs > 0) {
                    head = head.applySubst(frame.args.take(consumedArgs).asReversed())
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
    if (this.isWhnfByShape() &&
        (this !is Expression.Bvar || env.localCtxValue(localCtx, this.bvar) == null)
    ) {
        null
    } else if (localCtx.isEmpty() || this.maxLooseBVarIndex() < 0) {
        env.whnfCacheNoLevelSubst[this.ie]
    } else {
        env.whnfCacheWithCtxNoLevelSubst[ReduceCacheKey(this.ie, env.localCtxId(localCtx))]
    }

context(env: Environment)
private fun Expression.cacheWhnf(localCtx: List<Expression>, result: Expression) {
    if (this.isWhnfByShape() &&
        (this !is Expression.Bvar || env.localCtxValue(localCtx, this.bvar) == null)
    ) return
    if (localCtx.isEmpty() || this.maxLooseBVarIndex() < 0) {
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
    val localCtxId = if (this.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtx)
    val cacheKey = ReduceCacheKey(this.ie, localCtxId)
    if (env.natLiteralCacheNoLevelSubst.containsKey(cacheKey)) {
        return env.natLiteralCacheNoLevelSubst[cacheKey]
    }

    val result = this.tryRecognizeNatLiteralByWhnf(localCtx)
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
                if (!headConst.isNatLiteralPrimitiveConst()) return null

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
    return normalizedExpr.tryRecognizeNatLiteralCore(localCtx)
}

context(env: Environment)
private fun Expression.isNatLiteralPrimitiveConst(): Boolean = when (this) {
    is Expression.Const -> this.levels.isEmpty() && when (this.name.toStringDetailed()) {
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
    if (!headConst.isNatLiteralPrimitiveConst()) return null
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
    val boolType = env.findRootInductive("Bool")?.second
        ?: error("Nat literal reduction used without Bool inductive in environment")
    val shortName = if (value) "true" else "false"
    val ctorIndex = boolType.ctors.singleOrNull { ctorIndex ->
        val ctor = env.declarations[ctorIndex] as? Inductive.ConstructorVal
        (ctor?.name as? Name.Str)?.str == shortName
    }
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
    if (!headConst.isNatLiteralPrimitiveConst()) return null

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
private fun Expression.Proj.inferProjectionType(
    structType0: Expression,
    localCtx: List<Expression>,
): Expression {
    val structTypeExpr = structType0.whnf(localCtx = localCtx)
    val [structTypeHead, structTypeArgs] = structTypeExpr.unfoldApp()
    val structTypeConst = structTypeHead as? Expression.Const
        ?: error("Projection ${this.toStringDetailed()} expects structure type, got ${structTypeExpr.toStringDetailed()}")

    check(structTypeConst.name == this.typeNameExpr) {
        "Projection ${this.toStringDetailed()} type name mismatch: expected ${this.typeNameExpr}, got ${structTypeConst.name}"
    }

    // TODO: this used to be above the above check but it seems like some tests would accidentally fail on this linle instead of the right one
    val inductiveDecl = this.typeDecl as? Inductive.InductiveVal
        ?: error("Projection ${this.toStringDetailed()} expects inductive type declaration for ${this.typeNameExpr}")

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
    // The structure type was produced by inference above, and constructor binder types were
    // validated with the inductive declaration. Projection checking only needs their sorts;
    // recursively validating substituted projection arguments repeats the original derivation.
    val structSort = structTypeExpr.inferSort(localCtx = localCtx, validate = false)
    val isPropStructure = structSort.isLessOrEqual(Level.Zero)
    val nonPropFieldIndices = mutableSetOf<Int>()

    var ctorType: Expression = constructorDecl.typeExpr.instantiateLevelParams(projectionLevelSubst)
    repeat(constructorDecl.numParams + this.projIndex) { binderIndex ->
        val ctorForall = ctorType as? Expression.ForallE
            ?: error("Constructor ${constructorDecl.name} has too few binders while checking projection ${this.toStringDetailed()}")
        if (isPropStructure && binderIndex >= constructorDecl.numParams) {
            val priorFieldIndex = binderIndex - constructorDecl.numParams
            val priorFieldSort = ctorForall.typeExpr.inferSort(localCtx = localCtx, validate = false)
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
        val projectedSort = projectedType.inferSort(localCtx = localCtx, validate = false)
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
        val reducedExpr = rule.rhsExpr.instantiateLevelParams(recursorLevelSubst)
        val appliedArgs = (prefixArgs + fieldArgs + args.drop(majorArgIndex + 1))
            .map { it.instantiateLevelParams(levelSubst) }
        return reducedExpr.applyBetaArgs(appliedArgs)
    }

    fun tryReduceKRule(): Expression? {
        if (!recursorDecl.k) return null
        val kRule = recursorDecl.rules.singleOrNull() ?: return null
        if (kRule.nfields != 0) return null
        val kCtorDecl = env.constructorByName[kRule.ctorName] ?: return null
        if (kCtorDecl.numFields != 0 || kCtorDecl.numParams != recursorDecl.numParams) return null
        val majorExpr = args[majorArgIndex].instantiateLevelParams(levelSubst)
        val majorType = majorExpr.inferType(localCtx = localCtx, validate = false).whnf(localCtx = localCtx)
        val [majorTypeHead, majorTypeArgs] = majorType.unfoldApp()
        val majorTypeConst = majorTypeHead as? Expression.Const ?: return null
        if (majorTypeConst.name != kCtorDecl.inductName) return null
        if (majorTypeArgs.size != recursorDecl.numParams + recursorDecl.numIndices) return null

        val ctorNameIndex = env.nameIndices[kCtorDecl.name] ?: return null
        val ctorConst = env.addCustomExpr {
            Expression.Const(
                _name = ctorNameIndex,
                us = majorTypeConst.levels.map { level -> level.il },
                ie = it,
            )
        }
        val ctorExpr = ctorConst.applyArgs(majorTypeArgs.take(recursorDecl.numParams))
        val ctorType = ctorExpr.inferType(localCtx = localCtx, validate = false)
        val closedTypesEqual = majorType.maxLooseBVarIndex() < 0 &&
                ctorType.maxLooseBVarIndex() < 0 && majorType.closedDefEq(ctorType)
        if (!closedTypesEqual && !majorType.isDefEq(ctorType, localCtx, localCtx)) return null

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
        val etaInfo = recursorDecl.structureEtaInfo() ?: return@run
        val inductiveDeclIndex = etaInfo.inductiveDeclIndex
        val inductiveDecl = etaInfo.inductiveDecl
        val constructorDecl = etaInfo.constructorDecl
        val singleRule = etaInfo.rule

        val majorType = majorWhnf.inferType(localCtx = localCtx, validate = false).whnf(localCtx = localCtx)
        val majorTypeSpine = majorType.asAppSpine()
        val majorTypeHead = majorTypeSpine.first as? Expression.Const ?: return@run
        if (majorTypeHead.name != inductiveDecl.name) return@run
        if (majorTypeSpine.second.size != inductiveDecl.numParams) return@run
        if (majorType.inferSort(localCtx = localCtx, validate = false).isLessOrEqual(Level.Zero)) return@run

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
private fun Inductive.RecursorVal.structureEtaInfo(): StructureEtaRecursorInfo? {
    val cacheKey = this.name
    if (env.structureEtaRecursorCache.containsKey(cacheKey)) {
        return env.structureEtaRecursorCache[cacheKey]
    }

    val result = run {
        val singleRule = this.rules.singleOrNull() ?: return@run null
        val constructorDeclIndex = env.nameIndices[singleRule.ctorName] ?: return@run null
        val constructorDecl =
            env.declarations[constructorDeclIndex] as? Inductive.ConstructorVal ?: return@run null
        val inductiveDeclIndex = env.nameIndices[constructorDecl.inductName] ?: return@run null
        val inductiveDecl =
            env.declarations[inductiveDeclIndex] as? Inductive.InductiveVal ?: return@run null
        if (inductiveDecl.isRec || inductiveDecl.numIndices != 0 || inductiveDecl.ctors.size != 1) return@run null
        if (inductiveDecl.ctors.single() != constructorDeclIndex) return@run null
        if (constructorDecl.numParams != inductiveDecl.numParams) return@run null
        if (constructorDecl.numFields != singleRule.nfields) return@run null
        if (singleRule.ctorName != constructorDecl.name) return@run null

        StructureEtaRecursorInfo(inductiveDeclIndex, inductiveDecl, constructorDecl, singleRule)
    }
    env.structureEtaRecursorCache[cacheKey] = result
    return result
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

    val appliedArgs = listOf(ctorValueArg) +
            args.drop(arity).map { it.instantiateLevelParams(levelSubst) }
    return fnArg.applyBetaArgs(appliedArgs)
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
    if (!this.isScopedBy(localCtxLeft) || !other.isScopedBy(localCtxRight)) return false
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
        val valueType = value.inferType(localCtx = valueCtx, validate = false)
        val constructorType = constructorValue.inferType(localCtx = constructorCtx, validate = false)
        if (!valueType.isDefEq(constructorType, valueCtx, constructorCtx)) return false
        if (constructorType.inferSort(localCtx = constructorCtx, validate = false).isLessOrEqual(Level.Zero)) {
            return false
        }
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

    val leftType = this.inferType(localCtx = localCtxLeft, validate = false).whnf(localCtx = localCtxLeft)
    val typeHead = leftType.asAppSpine().first as? Expression.Const ?: return false
    val typeIndex = env.nameIndices[typeHead.name] ?: return false
    val inductive = env.declarations[typeIndex] as? Inductive.InductiveVal ?: return false
    if (inductive.isRec || inductive.numIndices != 0 || inductive.ctors.size != 1) return false
    if (leftType.inferSort(localCtx = localCtxLeft, validate = false).isLessOrEqual(Level.Zero)) return false
    val constructor = env.declarations[inductive.ctors.single()] as? Inductive.ConstructorVal ?: return false
    if (constructor.numFields != 0) return false
    return leftType.isDefEq(
        other.inferType(localCtx = localCtxRight, validate = false),
        localCtxLeft,
        localCtxRight,
    )
}

context(env: Environment)
private fun Expression.tryProofIrrelevanceDefEqNoLog(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    env.proofIrrelevanceAttempts += 1
    if (!this.canBeProofByShape() || !other.canBeProofByShape()) return false
    if (this.rigidProofStatus() == false || other.rigidProofStatus() == false) return false
    val tempLog = env.shouldLog
    env.shouldLog = false
    return try {
        this.tryProofIrrelevanceDefEq(other, localCtxLeft, localCtxRight).also { result ->
            if (result) env.proofIrrelevanceSuccesses += 1
        }
    } finally {
        env.shouldLog = tempLog
    }
}

private fun Expression.canBeProofByShape(): Boolean {
    return this !is Expression.ForallE &&
            this !is Expression.NatVal &&
            this !is Expression.Sort &&
            this !is Expression.StrVal
}

context(env: Environment)
private fun Expression.tryProofIrrelevanceDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    if (!this.isScopedBy(localCtxLeft) || !other.isScopedBy(localCtxRight)) return false
    val thisTy = this.inferType(localCtx = localCtxLeft, validate = false)
    if (!thisTy.inferSort(localCtx = localCtxLeft, validate = false).isLessOrEqual(Level.Zero)) return false
    return thisTy.isDefEq(
        other.inferType(localCtx = localCtxRight, validate = false),
        localCtxLeft,
        localCtxRight,
    )
}

context(env: Environment)
private fun Expression.isScopedBy(localCtx: List<Expression>): Boolean =
    this.maxLooseBVarIndex() < localCtx.size

context(env: Environment)
fun Expression.inferSort(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
    validate: Boolean = true,
): Level {
    val tyWhnf = this.inferType(levelSubst, localCtx, validate)
    val whnfTyExpr = tyWhnf.whnf(localCtx = localCtx)
    val sort = whnfTyExpr as? Expression.Sort
        ?: error("Expected Sort type for ${this.toStringDetailed()}, got ${whnfTyExpr.toStringDetailed()}")
    return sort.level
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
fun Expression.maxLooseBVarIndex(): Int {
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
fun Expression.dropOuterBinders(count: Int): Expression {
    if (count == 0 || this.maxLooseBVarIndex() < 0) return this
    return this.rewriteBinders { bvarExpr, depth ->
        when {
            bvarExpr.bvar < depth -> bvarExpr
            bvarExpr.bvar < depth + count ->
                error("Cannot drop binders: expression still references a removed binder")

            else -> env.addCustomExpr {
                bvarExpr.copy(bvar = bvarExpr.bvar - count, ie = it)
            }
        }
    }
}

context(env: Environment)
fun Expression.lift(amount: Int): Expression {
    if (amount == 0 || this.maxLooseBVarIndex() < 0) return this
    val cacheKey = ExprPairKey(this.ie, amount)
    env.liftCache[cacheKey]?.let { return it }
    val result = this.rewriteBinders { bvarExpr, depth ->
        if (bvarExpr.bvar >= depth) {
            env.addCustomExpr {
                bvarExpr.copy(bvar = bvarExpr.bvar + amount, ie = it)
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
    if (subst.isEmpty() || this.maxLooseBVarIndex() < 0) return this
    val singleSubstKey = subst.singleOrNull()?.let { ExprPairKey(this.ie, it.ie) }
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

    val result = this.rewriteBinders { bvarExpr, currentDepth ->
        when {
            bvarExpr.bvar < currentDepth -> bvarExpr
            bvarExpr.bvar - currentDepth < subst.size ->
                getLiftedSubst(bvarExpr.bvar - currentDepth, currentDepth)

            else -> {
                env.addCustomExpr {
                    bvarExpr.copy(bvar = bvarExpr.bvar - subst.size, ie = it)
                }
            }
        }
    }
    if (singleSubstKey != null) env.applySubstSingleCache[singleSubstKey] = result
    return result
}

private class BinderRewriteCache {
    private var keys = LongArray(16)
    private var values: Array<Expression?> = arrayOfNulls(16)
    private var size = 0

    private fun startIndex(key: Long): Int {
        val folded = (key xor (key ushr 32)).toInt()
        return (folded xor (folded ushr 16)) and (keys.size - 1)
    }

    operator fun get(key: Long): Expression? {
        var index = startIndex(key)
        while (true) {
            val value = values[index] ?: return null
            if (keys[index] == key) return value
            index = (index + 1) and (keys.size - 1)
        }
    }

    operator fun set(key: Long, value: Expression) {
        if ((size + 1) * 3 >= keys.size * 2) resize()
        insert(key, value)
    }

    private fun insert(key: Long, value: Expression) {
        var index = startIndex(key)
        while (true) {
            val current = values[index]
            if (current == null) {
                keys[index] = key
                values[index] = value
                size += 1
                return
            }
            if (keys[index] == key) {
                values[index] = value
                return
            }
            index = (index + 1) and (keys.size - 1)
        }
    }

    private fun resize() {
        val oldKeys = keys
        val oldValues = values
        keys = LongArray(oldKeys.size * 2)
        values = arrayOfNulls(keys.size)
        size = 0
        oldValues.forEachIndexed { index, value ->
            if (value != null) insert(oldKeys[index], value)
        }
    }
}

private class BinderRewriteStack {
    private var expressions: Array<Expression?> = arrayOfNulls(64)
    private var depths = IntArray(64)
    private var rebuilds = BooleanArray(64)
    private var cacheKeys = LongArray(64)
    private var size = 0

    fun add(expr: Expression, depth: Int, rebuild: Boolean = false, cacheKey: Long = 0L) {
        if (size == expressions.size) {
            expressions = expressions.copyOf(size * 2)
            depths = depths.copyOf(size * 2)
            rebuilds = rebuilds.copyOf(size * 2)
            cacheKeys = cacheKeys.copyOf(size * 2)
        }
        expressions[size] = expr
        depths[size] = depth
        rebuilds[size] = rebuild
        cacheKeys[size] = cacheKey
        size++
    }

    fun removeLastIndex(): Int {
        check(size > 0)
        size--
        return size
    }

    fun expressionAt(index: Int): Expression = expressions[index]!!
    fun depthAt(index: Int): Int = depths[index]
    fun rebuildAt(index: Int): Boolean = rebuilds[index]
    fun cacheKeyAt(index: Int): Long = cacheKeys[index]

    fun release(index: Int) {
        expressions[index] = null
    }

    fun isNotEmpty(): Boolean = size > 0
}

context(env: Environment)
private fun Expression.rewriteBinders(
    depth: Int = 0,
    rewriteBvar: (Expression.Bvar, Int) -> Expression
): Expression {
    val cache = BinderRewriteCache()
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
                makeLevelMax(newLeft, newRight)
            }
        }

        is Level.Imax -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                makeLevelImax(newLeft, newRight)
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
        .firstOrNull { [nameIndex, name] ->
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