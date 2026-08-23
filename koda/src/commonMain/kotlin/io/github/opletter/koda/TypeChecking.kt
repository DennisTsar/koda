package io.github.opletter.koda

private var debugClosedEvaluation = false
private var debugTargetDeclaration = false
private const val debugTargetIndex = -1//21_000_000///51_500_000

fun NamedDecl.hasDistinctLevelParams(): Boolean =
    levelParamIndices.toSet().size == levelParamIndices.size

internal data class StructureEtaRecursorInfo(
    val inductiveDeclIndex: Int,
    val inductiveDecl: Inductive.InductiveVal,
    val constructorDecl: Inductive.ConstructorVal,
    val rule: Inductive.RecursorVal.RecursorRule,
)

fun typeCheck(data: Sequence<ExportType>) {
    val env = Environment()
//    typeCheck(data, env = env)
    context(env) {
        _typeCheck(data)
    }
}

context(env: Environment)
fun _typeCheck(rawData: Sequence<ExportType>) {
//    val debugTimingRanges = emptyList<IntRange>()
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
                is Expression -> {
                    data.registerInto(env)
                    env.recordExpressionReferences(data)
                }
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
                env.recordExpressionReferences(data)
            }

            is Declaration -> {
                // (1): "the declaration is not already declared in the environment"
                data.registerInto(env)
                // (2): "has no duplicate universe parameters"
                // not the most efficient check but probably doesn't matter?
                check(data.hasDistinctLevelParams()) { "Duplicate universe parameters in $data" }
                // (3): "the declaration's type is actually a type and not a value (that infer declar.ty returns an expression Sort <n>)"
//                println("found type: ${data.typeExpr.toStringDetailed()}")
//                val debugStart = env.clock.elapsedNow()
                try {
                    val declaredTypeSortLevel = data.typeExpr.inferSort()
                    val value = when (data) {
                        is Declaration.Def -> data.valueExpr
                        is Declaration.Opaque -> data.valueExpr // TODO: treat opqaue differently
                        is Declaration.Thm -> data.valueExpr
                        is Declaration.Axiom, is Declaration.Quot -> null
                    }
                    if (value != null) {
                        check(typeCheckDeclaration(value, data.typeExpr)) {
                            "value not defeq to type for ${data.name.toStringDetailed()} $data"
                        }
                    }
                    if (data is Declaration.Thm) {
                        check(declaredTypeSortLevel.isLessOrEqual(Level.Zero)) {
                            "The type of a theorem has to be a proposition: found ${data.typeExpr.toStringDetailed()}"
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
                "stats: defEqCalls=${env.defEqCalls} defEqFailureCacheHits=${env.defEqFailureCacheHits} " +
                        "defEqFailures=${env.defEqFailures?.size ?: 0}"
            )
        }
        if (data is Declaration || data is Inductive) {
            if (data is Declaration) {
                val declarationElapsed = env.clock.elapsedNow() - itemStart
                if (declarationElapsed.inWholeMilliseconds >= 1_000) {
                    val declarationStats = """
                        defEqCalls=${env.defEqCalls} defEqFailures=${env.defEqFailures?.size ?: 0}
                        inferCache=${env.inferTypeCacheNoLevelSubst.size}
                        whnfCache=${env.whnfCacheNoLevelSubst.size + env.whnfCacheWithCtxNoLevelSubst.size}
                        proofIrrelevance=${env.proofIrrelevanceSuccesses}/${env.proofIrrelevanceAttempts}
                        typedProofSkips=${env.typedCongruenceProofSkips}
                    """.trimIndent().replace('\n', ' ')
                    println(
                        "slow declaration: name=${data.name.toStringDetailed()} index=$index " +
                                "elapsed=$declarationElapsed $declarationStats"
                    )
                }
            }
            env.clearCustom()
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
private fun Expression.Const.proofArgumentMask(arity: Int): BooleanArray? {
    val key = (this.ie.toLong() shl 32) xor (arity.toLong() and 0xffffffffL)
    if (env.proofArgumentMaskCache.containsKey(key)) return env.proofArgumentMaskCache[key]
    var type = this.inferType(validate = false)
    var localCtx = emptyList<Expression>()
    val result = BooleanArray(arity) {
        val forall = type.whnf(localCtx = localCtx) as? Expression.ForallE
            ?: return run { env.proofArgumentMaskCache[key] = null; null }
        val domainIsProp = forall.typeExpr
            .inferSort(localCtx = localCtx, validate = false)
            .isLessOrEqual(Level.Zero)
        localCtx = env.consLocalCtx(forall.typeExpr, localCtx)
        type = forall.bodyExpr
        domainIsProp
    }
    env.proofArgumentMaskCache[key] = result
    return result
}

context(env: Environment)
fun typeCheckDeclaration(value: Expression, expectedType: Expression): Boolean {
    if (env.shouldLog) println("found value: ${value/*.toStringDetailed()*/}")
    var valueExpr = value
    var expectedExpr = expectedType
    var valueCtx = emptyList<Expression>()
    var expectedCtx = emptyList<Expression>()
    while (true) {
        if (valueExpr is Expression.Mdata) {
            valueExpr = valueExpr.expr
            continue
        }
        val lambda = valueExpr as? Expression.Lam ?: break
        val expectedForall = expectedExpr.whnf(localCtx = expectedCtx) as? Expression.ForallE ?: break
        lambda.typeExpr.inferSort(localCtx = valueCtx)
        if (!expectedForall.typeExpr.isDefEq(lambda.typeExpr, expectedCtx, valueCtx)) return false
        expectedCtx = env.consLocalCtx(expectedForall.typeExpr, expectedCtx)
        valueCtx = env.consLocalCtx(lambda.typeExpr, valueCtx)
        expectedExpr = expectedForall.bodyExpr
        valueExpr = lambda.bodyExpr
    }

    val inferredValueType = valueExpr.inferType(localCtx = valueCtx)
    if (env.shouldLog) println("inferred type of value: ${inferredValueType/*.toStringDetailed()*/}")
    if (env.shouldLog) {
        println("expected type detailed: ${expectedExpr.toStringDetailed()}")
        println("inferred type detailed: ${inferredValueType.toStringDetailed()}")
    }
    return expectedExpr.isDefEq(inferredValueType, expectedCtx, valueCtx)
}

@Suppress("NOTHING_TO_INLINE")
context(env: Environment)
private inline fun Expression.Const.hasSameNameAndLevels(other: Expression.Const): Boolean {
    return this.name == other.name && this.levels.isEqual(other.levels)
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
    val leftCtxId = if (this.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxLeft)
    val rightCtxId = if (other.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxRight)
    if (env.defEqEquivalences.areEquivalent(this.ie, leftCtxId, other.ie, rightCtxId)) return true
    env.defEqFailures?.let { failures ->
        if (this.defEqCacheKey(other, leftCtxId, rightCtxId) in failures) {
            env.defEqFailureCacheHits += 1
            return false
        }
    }
    fun finish(value: Boolean): Boolean {
        if (value) {
            env.defEqEquivalences.addEquivalent(this.ie, leftCtxId, other.ie, rightCtxId)
        } else {
            val failures = env.defEqFailures ?: mutableSetOf<DefEqCacheKey>().also { env.defEqFailures = it }
            failures += this.defEqCacheKey(other, leftCtxId, rightCtxId)
        }
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
    if (this.tryProofIrrelevanceDefEqNoLog(other, localCtxLeft, localCtxRight)) return finish(true)

//    if (traceDefEq) println("debug defeq phase: cheap whnf")
    val leftCore = this.whnfCore(localCtxLeft, cheapProjection = true)
    val rightCore = other.whnfCore(localCtxRight, cheapProjection = true)
//    if (traceDefEq) println("debug defeq phase: core quick")
    leftCore.quickIsDefEq(rightCore, localCtxLeft, localCtxRight)?.let { return finish(it) }
    leftCore.tryStructuralDefEq(rightCore)?.let { return finish(it) }
    if (leftCore.tryKnownDefEqCongruence(rightCore, localCtxLeft, localCtxRight)) return finish(true)

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
    var locals: ClosedEvalEnv = ClosedEvalEnv.Empty
    for (index in indices.reversed()) {
        val value = env.localCtxValue(this, index)
        val isProof = this[index].rigidTypeIsProp()
        val closure = if (value == null) {
            ClosedClosure(Expression.Bvar(index, Int.MIN_VALUE), ClosedEvalEnv.Empty, isProof)
        } else {
            ClosedClosure(value, locals, isProof)
        }
        locals = ClosedEvalEnv.Bind(closure, locals)
    }
    return locals
}

context(env: Environment)
private fun Expression.tryClosedBoolTrueDefEq(other: Expression, localCtx: List<Expression>): Boolean? {
    if (other.boolValue() != true || this.maxLooseBVarIndex() >= 0 && !env.eagerReduction) return null
//    val start = env.clock.elapsedNow()
    val value = ClosedClosure(this, localCtx.closedEvalEnv()).closedWhnf(trace = debugTargetDeclaration)
        ?: return null
    val result = if (value.arguments.isEmpty()) value.head.expression.boolValue() else null
    return result
//        .also {
//        if (debugClosedEvaluation || debugTargetDeclaration) {
//            println("closed Bool evaluation: expr=${this.ie} result=$result elapsed=${env.clock.elapsedNow() - start}")
//        }
//    }
}

context(env: Environment)
private fun Expression.boolValue(): Boolean? {
    val constant = this as? Expression.Const ?: return null
    val constructorName = constant.name as? Name.Str ?: return null
    val boolName = env.names[constructorName.pre] as? Name.Str ?: return null
    if (boolName.pre != 0 || boolName.str != "Bool") return null
    return when (constructorName.str) {
        "false" -> false
        "true" -> true
        else -> null
    }
}

private sealed interface ClosedEvalEnv {
    data object Empty : ClosedEvalEnv
    class Bind(val value: ClosedClosure, val tail: ClosedEvalEnv) : ClosedEvalEnv
}

private class ClosedClosure(
    var expression: Expression,
    var locals: ClosedEvalEnv,
    var isProof: Boolean = false,
    val pendingArguments: List<ClosedClosure> = emptyList(),
) {
    var cachedArguments: List<ClosedClosure>? = null
}

private data class ClosedValue(
    val head: ClosedClosure,
    val arguments: List<ClosedClosure>,
)

private data class ClosedLocalLookup(
    val closure: ClosedClosure?,
    val neutralIndex: Int,
)

private data class ClosedDefEqTask(
    val left: ClosedClosure,
    val right: ClosedClosure,
    val nextNeutral: Int,
    val sameTypeKnown: Boolean,
    val expectedType: ClosedExpectedType? = null,
)

private sealed interface ClosedExpectedType {
    data class Closure(val value: ClosedClosure) : ClosedExpectedType

    data class ConstantArgument(
        val head: Expression.Const,
        val arguments: List<ClosedClosure>,
        val index: Int,
    ) : ClosedExpectedType
}

private data class ClosedDefEqState(
    val leftExpressionId: Int,
    val leftLocals: ClosedEvalEnv,
    val leftArguments: List<ClosedClosure>,
    val rightExpressionId: Int,
    val rightLocals: ClosedEvalEnv,
    val rightArguments: List<ClosedClosure>,
    val nextNeutral: Int,
    val sameTypeKnown: Boolean,
    val expectedType: ClosedExpectedType?,
)

private data class ClosedRecursorRuleKey(
    val recursorName: Name,
    val levelIds: List<Int>,
    val ruleExprId: Int,
)

private enum class NatPrimitive(val arity: Int) {
    Succ(1), Add(2), Sub(2), Mul(2), Pow(2), Div(2), Mod(2), Beq(2), Ble(2)
}

private sealed interface ClosedEvalContinuation {
    data class Force(
        val closure: ClosedClosure,
        val outerArgs: List<ClosedClosure>,
    ) : ClosedEvalContinuation

    data class Projection(
        val projection: Expression.Proj,
        val locals: ClosedEvalEnv,
        val outerArgs: List<ClosedClosure>,
        val unfoldDefinitions: Boolean,
    ) : ClosedEvalContinuation

    data class Quotient(
        val quotConst: Expression.Const,
        val quotient: Declaration.Quot,
        val arguments: List<ClosedClosure>,
        val arity: Int,
        val unfoldDefinitions: Boolean,
    ) : ClosedEvalContinuation

    data class Recursor(
        val recursorConst: Expression.Const,
        val recursor: Inductive.RecursorVal,
        val recursorArgs: List<ClosedClosure>,
        val unfoldDefinitions: Boolean,
    ) : ClosedEvalContinuation

    data class NatOperand(
        val primitiveConst: Expression.Const,
        val primitive: NatPrimitive,
        val operands: List<ClosedClosure>,
        val extraArgs: List<ClosedClosure>,
        val values: List<NatValue>,
    ) : ClosedEvalContinuation
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
    val instantiatedRecursorRules = mutableMapOf<ClosedRecursorRuleKey, Expression>()
    val looseBvarIndices = mutableMapOf<Int, List<Int>>()

    fun bindingAt(locals: ClosedEvalEnv, index: Int): ClosedClosure? {
        var current = locals
        var remaining = index
        while (current is ClosedEvalEnv.Bind) {
            if (remaining == 0) return current.value
            remaining -= 1
            current = current.tail
        }
        return null
    }

    fun closuresObviouslyEqual(left: ClosedClosure, right: ClosedClosure): Boolean {
        if (left.isProof && right.isProof) return true
        if (left === right) return true
        if (
            left.expression === right.expression && left.locals === right.locals &&
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
    ): Boolean {
        for (index in referencedLooseBvars(expression)) {
            val leftBinding = bindingAt(left, index) ?: return false
            val rightBinding = bindingAt(right, index) ?: return false
            if (!closuresObviouslyEqual(leftBinding, rightBinding)) {
                pending.addLast(ClosedDefEqTask(leftBinding, rightBinding, nextNeutral, true))
            }
        }
        return true
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

    fun projectClosedValue(value: ClosedValue, inductiveIndex: Int, fieldIndex: Int): ClosedClosure {
        val valueClosure = ClosedClosure(
            value.head.expression,
            value.head.locals,
            value.head.isProof,
            pendingArguments = value.arguments,
        )
        val valueRef = env.addCustomExpr { Expression.Bvar(0, it) }
        val projection = env.addCustomExpr {
            Expression.Proj(typeName = inductiveIndex, idx = fieldIndex, struct = valueRef.ie, ie = it)
        }
        return ClosedClosure(
            projection,
            ClosedEvalEnv.Bind(valueClosure, ClosedEvalEnv.Empty),
        )
    }

    fun resolveExpectedType(expectedType: ClosedExpectedType?): ClosedClosure? = when (expectedType) {
        null -> null
        is ClosedExpectedType.Closure -> expectedType.value
        is ClosedExpectedType.ConstantArgument -> {
            var type = ClosedClosure(expectedType.head.inferType(validate = false), ClosedEvalEnv.Empty)
            for (index in 0..expectedType.index) {
                val typeValue = type.closedWhnf(instantiatedRecursorRules, trace) ?: return null
                if (typeValue.arguments.isNotEmpty()) return null
                val forall = typeValue.head.expression as? Expression.ForallE ?: return null
                if (index == expectedType.index) {
                    return ClosedClosure(forall.typeExpr, typeValue.head.locals)
                }
                val argument = expectedType.arguments.getOrNull(index) ?: return null
                type = ClosedClosure(
                    forall.bodyExpr,
                    ClosedEvalEnv.Bind(argument, typeValue.head.locals),
                )
            }
            null
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
                pendingArguments = argumentType.arguments.take(constructor.numParams),
            )
        )
    }

    fun deltaStep(value: ClosedValue): Pair<LazyDeltaStep, ClosedClosure>? {
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

    fun unfoldDeltaStep(step: Pair<LazyDeltaStep, ClosedClosure>): ClosedValue? =
        step.second.closedWhnf(instantiatedRecursorRules, trace, unfoldDefinitionsAtRoot = false)

    fun headsCanBeCompared(left: ClosedValue, right: ClosedValue): Boolean {
        val leftHead = left.head.expression
        val rightHead = right.head.expression
        return when {
            leftHead is Expression.Const && rightHead is Expression.Const ->
                leftHead.hasSameNameAndLevels(rightHead)

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
        while (!headsCanBeCompared(left, right)) {
            val leftStep = deltaStep(left)
            val rightStep = deltaStep(right)
            when (chooseLazyDeltaSide(leftStep?.first, rightStep?.first)) {
                LazyDeltaChoice.Left -> left = unfoldDeltaStep(leftStep!!) ?: return null
                LazyDeltaChoice.Right -> right = unfoldDeltaStep(rightStep!!) ?: return null
                LazyDeltaChoice.Both -> {
                    left = unfoldDeltaStep(leftStep!!) ?: return null
                    right = unfoldDeltaStep(rightStep!!) ?: return null
                }

                null -> break
            }
        }
        return left to right
    }

    pending.addLast(ClosedDefEqTask(this, other, nextNeutral, expectedType != null, expectedType))
    while (pending.isNotEmpty()) {
        val task = pending.removeLast()
        if (task.left.isProof && task.right.isProof) continue
        if (resolveExpectedType(task.expectedType)?.expression?.rigidTypeIsProp() == true) continue
        val state = ClosedDefEqState(
            task.left.expression.ie,
            task.left.locals,
            task.left.pendingArguments,
            task.right.expression.ie,
            task.right.locals,
            task.right.pendingArguments,
            task.nextNeutral,
            task.sameTypeKnown,
            task.expectedType,
        )
        if (!visited.add(state)) continue
        fun fail(reason: String, left: ClosedValue? = null, right: ClosedValue? = null): Boolean {
//            if (trace) {
//                println(
//                    "debug closure equality failed: $reason " +
//                            "left=${task.left.expression.debugHead()} right=${task.right.expression.debugHead()} " +
//                            "leftWhnf=${left?.head?.expression?.debugHead()}(${left?.arguments?.size}) " +
//                            "rightWhnf=${right?.head?.expression?.debugHead()}(${right?.arguments?.size})"
//                )
//            }
            return false
        }
        if (
            task.left.expression === task.right.expression &&
            task.left.pendingArguments.size == task.right.pendingArguments.size &&
            task.left.pendingArguments.indices.all {
                task.left.pendingArguments[it] === task.right.pendingArguments[it]
            }
        ) {
            if (task.left.locals === task.right.locals) continue
            if (
                enqueueEnvironmentAgreement(
                    task.left.expression,
                    task.left.locals,
                    task.right.locals,
                    task.nextNeutral,
                )
            ) continue else return fail("missing environment binding")
        }
        val [left, right] = unfoldForComparison(task.left, task.right)
            ?: return fail("closure reduction stuck")

        val leftProjection = left.head.expression as? Expression.Proj
        val rightProjection = right.head.expression as? Expression.Proj
        if (leftProjection != null && rightProjection != null) {
            if (left.arguments.size != right.arguments.size) return fail("projection arity", left, right)
            if (
                leftProjection.typeNameExpr != rightProjection.typeNameExpr ||
                leftProjection.projIndex != rightProjection.projIndex
            ) return fail("projection heads", left, right)
            pending.addLast(
                ClosedDefEqTask(
                    ClosedClosure(leftProjection.structExpr, left.head.locals),
                    ClosedClosure(rightProjection.structExpr, right.head.locals),
                    task.nextNeutral,
                    true,
                    enclosingStructureType(task.expectedType),
                )
            )
            left.arguments.forEachIndexed { index, left ->
                pending.addLast(
                    ClosedDefEqTask(
                        left, right.arguments[index], task.nextNeutral, true,
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
                for (fieldIndex in 0 until constructor.numFields) {
                    pending.addLast(
                        ClosedDefEqTask(
                            left.arguments[constructor.numParams + fieldIndex],
                            projectClosedValue(right, inductiveIndex, fieldIndex),
                            task.nextNeutral,
                            true,
                            ClosedExpectedType.ConstantArgument(
                                constructorConst,
                                left.arguments,
                                constructor.numParams + fieldIndex,
                            ),
                        )
                    )
                }
                continue
            }
            if (rightEta != null && leftEta == null && !leftIsAnyConstructor) {
                val [inductiveIndex, constructor] = rightEta
                val constructorConst = right.head.expression as Expression.Const
                for (fieldIndex in 0 until constructor.numFields) {
                    pending.addLast(
                        ClosedDefEqTask(
                            projectClosedValue(left, inductiveIndex, fieldIndex),
                            right.arguments[constructor.numParams + fieldIndex],
                            task.nextNeutral,
                            true,
                            ClosedExpectedType.ConstantArgument(
                                constructorConst,
                                right.arguments,
                                constructor.numParams + fieldIndex,
                            ),
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
                neutralDomain.rigidTypeIsProp(),
            )

            fun applyNeutral(value: ClosedValue, lambda: Expression.Lam?): ClosedClosure {
                if (lambda != null) {
                    return ClosedClosure(
                        lambda.bodyExpr,
                        ClosedEvalEnv.Bind(neutral, value.head.locals),
                    )
                }
                return ClosedClosure(
                    value.head.expression,
                    value.head.locals,
                    pendingArguments = value.arguments + neutral,
                )
            }
            pending.addLast(
                ClosedDefEqTask(
                    applyNeutral(left, leftLambda),
                    applyNeutral(right, rightLambda),
                    task.nextNeutral - 1,
                    true,
                    applyExpectedFunctionType(task.expectedType, neutral),
                )
            )
            if (leftLambda != null && rightLambda != null) {
                pending.addLast(
                    ClosedDefEqTask(
                        ClosedClosure(leftLambda.typeExpr, left.head.locals),
                        ClosedClosure(rightLambda.typeExpr, right.head.locals),
                        task.nextNeutral,
                        true,
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
                    forall.typeExpr.rigidTypeIsProp(),
                )

                fun applyNeutral(value: ClosedValue): ClosedClosure = ClosedClosure(
                    value.head.expression,
                    value.head.locals,
                    pendingArguments = value.arguments + neutral,
                )
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
                    )
                )
                continue
            }
        }

        if (left.arguments.size != right.arguments.size) return fail("spine arity", left, right)

        val leftForall = left.head.expression as? Expression.ForallE
        val rightForall = right.head.expression as? Expression.ForallE
        if (leftForall != null && rightForall != null && left.arguments.isEmpty()) {
            val neutral = ClosedClosure(
                Expression.Bvar(task.nextNeutral, Int.MIN_VALUE),
                ClosedEvalEnv.Empty,
                leftForall.typeExpr.rigidTypeIsProp() && rightForall.typeExpr.rigidTypeIsProp(),
            )
            pending.addLast(
                ClosedDefEqTask(
                    ClosedClosure(leftForall.bodyExpr, ClosedEvalEnv.Bind(neutral, left.head.locals)),
                    ClosedClosure(rightForall.bodyExpr, ClosedEvalEnv.Bind(neutral, right.head.locals)),
                    task.nextNeutral - 1,
                    true,
                )
            )
            pending.addLast(
                ClosedDefEqTask(
                    ClosedClosure(leftForall.typeExpr, left.head.locals),
                    ClosedClosure(rightForall.typeExpr, right.head.locals),
                    task.nextNeutral,
                    true,
                )
            )
            continue
        }

        fun ClosedValue.natValueOrNull(): NatValue? {
            if (this.arguments.isNotEmpty()) return null
            return when (val expression = this.head.expression) {
                is Expression.NatVal -> expression.natVal
                else -> if (expression.isNatZeroCtorConst()) NatValue.ZERO else null
            }
        }

        val leftNat = left.natValueOrNull()
        val rightNat = right.natValueOrNull()
        if (leftNat != null || rightNat != null) {
            if (leftNat == null || leftNat != rightNat) return fail("natural literals", left, right)
            continue
        }

        val leftHead = left.head.expression
        val rightHead = right.head.expression
        val headsMatch = when {
            leftHead is Expression.Const && rightHead is Expression.Const ->
                leftHead.hasSameNameAndLevels(rightHead)

            leftHead is Expression.Sort && rightHead is Expression.Sort ->
                leftHead.level.isEqual(rightHead.level)

            leftHead is Expression.StrVal && rightHead is Expression.StrVal ->
                leftHead.strVal == rightHead.strVal

            leftHead is Expression.Bvar && rightHead is Expression.Bvar ->
                leftHead.bvar == rightHead.bvar

            else -> false
        }
        if (!headsMatch) return fail("neutral heads", left, right)
        val proofArguments = (left.head.expression as? Expression.Const)
            ?.proofArgumentMask(left.arguments.size)
        for (index in left.arguments.indices) {
            if (proofArguments?.get(index) == true) continue
            val expectedType = (leftHead as? Expression.Const)?.let { head ->
                ClosedExpectedType.ConstantArgument(head, left.arguments, index)
            }
            pending.addLast(
                ClosedDefEqTask(
                    left.arguments[index],
                    right.arguments[index],
                    task.nextNeutral,
                    true,
                    expectedType,
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

context(env: Environment)
private fun ClosedClosure.closedWhnf(
    instantiatedRecursorRules: MutableMap<ClosedRecursorRuleKey, Expression> = mutableMapOf(),
    trace: Boolean = false,
    unfoldDefinitionsAtRoot: Boolean = true,
): ClosedValue? {
    var currentExpression = this.expression
    var currentLocals = this.locals
    val argumentStack = ArrayDeque<ClosedClosure>()
    argumentStack.addAll(this.cachedArguments ?: this.pendingArguments)
    val continuations = mutableListOf<ClosedEvalContinuation>()
//    var steps = 0L
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

    fun setArgsInOrder(arguments: List<ClosedClosure>) {
        argumentStack.clear()
        argumentStack.addAll(arguments)
    }

    fun setCurrent(closure: ClosedClosure) {
        currentExpression = closure.expression
        currentLocals = closure.locals
    }

    fun argumentsOf(closure: ClosedClosure): List<ClosedClosure> =
        closure.cachedArguments ?: closure.pendingArguments

    fun lookupLocal(locals: ClosedEvalEnv, index: Int): ClosedLocalLookup {
        var currentLocals = locals
        var remaining = index
        while (currentLocals is ClosedEvalEnv.Bind) {
            if (remaining == 0) return ClosedLocalLookup(currentLocals.value, 0)
            remaining -= 1
            currentLocals = currentLocals.tail
        }
        return ClosedLocalLookup(null, remaining)
    }

    fun terminalNatValue(): NatValue? {
        if (argumentStack.isNotEmpty()) return null
        return when (val expression = currentExpression) {
            is Expression.NatVal -> expression.natVal
            else -> if (expression.isNatZeroCtorConst()) NatValue.ZERO else null
        }
    }

    fun transientNat(value: NatValue): Expression.NatVal =
        Expression.NatVal(value, Int.MIN_VALUE)

    fun tryKRule(
        recursorConst: Expression.Const,
        recursor: Inductive.RecursorVal,
        recursorArgs: List<ClosedClosure>,
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
            if (forall.typeExpr.rigidTypeIsProp()) recursorArgs[parameterIndex].isProof = true
            constructorResult = ClosedClosure(
                forall.bodyExpr,
                ClosedEvalEnv.Bind(recursorArgs[parameterIndex], constructorResult.locals),
            )
        }

        val resultType = constructorResult.closedWhnf(instantiatedRecursorRules)
            ?: return fail("constructor result reduction")
        val resultHead = resultType.head.expression as? Expression.Const ?: return fail("constructor result head")
        if (resultHead.name != constructor.inductName) return fail("constructor result inductive")
        val actualTypeArgs = recursorArgs.take(recursor.numParams) +
                recursorArgs.subList(prefixSize, majorIndex)
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
        recursorArgs: List<ClosedClosure>,
        rule: Inductive.RecursorVal.RecursorRule,
        fieldArgs: List<ClosedClosure>,
    ) {
        val prefixSize = recursor.numParams + recursor.numMotives + recursor.numMinors
        val majorIndex = prefixSize + recursor.numIndices
        val cacheKey = ClosedRecursorRuleKey(
            recursorConst.name,
            recursorConst.levels.map { it.il },
            rule.rhsExpr.ie,
        )
        currentExpression = instantiatedRecursorRules.getOrPut(cacheKey) {
            val levelSubst = recursorConst.composeLevelSubst(emptyMap())
            rule.rhsExpr.instantiateLevelParams(levelSubst)
        }
        currentLocals = ClosedEvalEnv.Empty
        argumentStack.clear()

        fun applyArgument(argument: ClosedClosure) {
            val lambda = currentExpression as? Expression.Lam
            if (lambda != null && argumentStack.isEmpty()) {
                if (lambda.typeExpr.rigidTypeIsProp()) argument.isProof = true
//                betaReductions += 1
                currentExpression = lambda.bodyExpr
                currentLocals = ClosedEvalEnv.Bind(argument, currentLocals)
            } else {
                argumentStack.addLast(argument)
            }
        }

        (recursorArgs.take(prefixSize) + fieldArgs + recursorArgs.drop(majorIndex + 1)).forEach {
            applyArgument(it)
        }
    }

    while (true) {
//        steps += 1
//        if (trace && steps % 1_000_000L == 0L) {
//            println(
//                "debug evaluator progress: steps=$steps current=${currentExpression.debugHead()} " +
//                        "args=${argumentStack.size} continuations=${continuations.size} " +
//                        "beta=$betaReductions delta=$deltaReductions recursors=$recursorReductions"
//            )
//        }
        if (currentIsWhnf) {
            currentIsWhnf = false
        } else when (val expression = currentExpression) {
            is Expression.App -> {
//                applications += 1
                argumentStack.addFirst(ClosedClosure(expression.argExpr, currentLocals))
                currentExpression = expression.fnExpr
                continue
            }

            is Expression.Bvar -> {
                val lookup = lookupLocal(currentLocals, expression.bvar)
                val binding = lookup.closure
                if (binding == null) {
                    currentExpression = Expression.Bvar(lookup.neutralIndex, Int.MIN_VALUE)
                    currentLocals = ClosedEvalEnv.Empty
                } else {
                    val cachedArguments = binding.cachedArguments
                    if (cachedArguments == null) {
                        continuations += ClosedEvalContinuation.Force(binding, argumentStack.toList())
                        setCurrent(binding)
                        setArgsInOrder(binding.pendingArguments)
                    } else {
                        setCurrent(binding)
                        setArgsInOrder(cachedArguments + argumentStack)
                    }
                    continue
                }
            }

            is Expression.Lam -> {
                if (argumentStack.isNotEmpty()) {
//                    betaReductions += 1
                    val argument = argumentStack.removeFirst()
                    if (expression.typeExpr.rigidTypeIsProp()) argument.isProof = true
                    currentExpression = expression.bodyExpr
                    currentLocals = ClosedEvalEnv.Bind(argument, currentLocals)
                    continue
                }
            }

            is Expression.LetE -> {
                val value = ClosedClosure(
                    expression.valueExpr,
                    currentLocals,
                    expression.typeExpr.rigidTypeIsProp(),
                )
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
                    argumentStack.toList(),
                    unfoldDefinitions,
                )
                currentExpression = expression.structExpr
                argumentStack.clear()
                unfoldDefinitions = true
                continue
            }

            is Expression.Const -> {
                val quotient = expression.decl as? Declaration.Quot
                if (
                    quotient != null &&
                    (quotient.kind == Declaration.Quot.Kind.Lift ||
                            quotient.kind == Declaration.Quot.Kind.Ind)
                ) {
                    val arity = quotient.typeExpr.forallBinderCount()
                    if (arity > 0 && argumentStack.size >= arity) {
                        val arguments = argumentStack.toList()
                        continuations += ClosedEvalContinuation.Quotient(
                            expression,
                            quotient,
                            arguments,
                            arity,
                            unfoldDefinitions,
                        )
                        setCurrent(arguments[arity - 1])
                        setArgsInOrder(argumentsOf(arguments[arity - 1]))
                        unfoldDefinitions = true
                        continue
                    }
                }

                val recursor = expression.decl as? Inductive.RecursorVal
                if (recursor != null) {
                    val majorIndex = recursor.numParams + recursor.numMotives +
                            recursor.numMinors + recursor.numIndices
                    if (majorIndex < argumentStack.size) {
                        val arguments = argumentStack.toList()
                        val kRule = tryKRule(expression, recursor, arguments)
                        if (kRule != null) {
//                            recursorReductions += 1
//                            incrementCount(recursorCounts, expression.name)
                            applyRecursorRule(expression, recursor, arguments, kRule, emptyList())
                            continue
                        }
                        continuations += ClosedEvalContinuation.Recursor(
                            expression,
                            recursor,
                            arguments,
                            unfoldDefinitions,
                        )
                        setCurrent(arguments[majorIndex])
                        setArgsInOrder(argumentsOf(arguments[majorIndex]))
                        unfoldDefinitions = true
                        continue
                    }
                }

                val primitive = if (unfoldDefinitions) expression.natPrimitive() else null
                if (primitive != null && argumentStack.size >= primitive.arity) {
                    val arguments = argumentStack.toList()
                    val operands = arguments.take(primitive.arity)
                    continuations += ClosedEvalContinuation.NatOperand(
                        primitiveConst = expression,
                        primitive = primitive,
                        operands = operands,
                        extraArgs = arguments.drop(primitive.arity),
                        values = emptyList(),
                    )
                    setCurrent(operands.first())
                    setArgsInOrder(argumentsOf(operands.first()))
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
            return ClosedValue(ClosedClosure(currentExpression, currentLocals), argumentStack.toList())
        }

        when (val continuation = continuations.removeAt(continuations.lastIndex)) {
            is ClosedEvalContinuation.Force -> {
                val valueArguments = argumentStack.toList()
                continuation.closure.expression = currentExpression
                continuation.closure.locals = currentLocals
                continuation.closure.cachedArguments = valueArguments
                setArgsInOrder(valueArguments + continuation.outerArgs)
            }

            is ClosedEvalContinuation.Projection -> {
                unfoldDefinitions = continuation.unfoldDefinitions
                val head = currentExpression as? Expression.Const
                val constructor = head?.decl as? Inductive.ConstructorVal
                if (head == null || constructor == null) {
                    currentExpression = continuation.projection
                    currentLocals = continuation.locals
                    setArgsInOrder(continuation.outerArgs)
                    currentIsWhnf = true
                    continue
                }
                if (constructor.inductName != continuation.projection.typeNameExpr) return fail("projection type")
                val fieldIndex = constructor.numParams + continuation.projection.projIndex
                val field = argumentStack.getOrNull(fieldIndex) ?: return fail("projection field")
                setCurrent(field)
                setArgsInOrder(argumentsOf(field) + continuation.outerArgs)
            }

            is ClosedEvalContinuation.Quotient -> {
                unfoldDefinitions = continuation.unfoldDefinitions
                val majorHead = currentExpression as? Expression.Const
                val majorCtor = majorHead?.decl as? Declaration.Quot
                if (majorHead == null || majorCtor?.kind != Declaration.Quot.Kind.Ctor) {
                    currentExpression = continuation.quotConst
                    currentLocals = ClosedEvalEnv.Empty
                    setArgsInOrder(continuation.arguments)
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
                setCurrent(function)
                setArgsInOrder(
                    argumentsOf(function) + ctorValue + continuation.arguments.drop(continuation.arity)
                )
            }

            is ClosedEvalContinuation.Recursor -> {
                unfoldDefinitions = continuation.unfoldDefinitions
//                recursorReductions += 1
//                incrementCount(recursorCounts, continuation.recursorConst.name)
                val majorNat = terminalNatValue()
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
                    val majorHead = currentExpression as? Expression.Const
                    val constructor = majorHead?.decl as? Inductive.ConstructorVal
                    if (majorHead == null || constructor == null) {
                        currentExpression = continuation.recursorConst
                        currentLocals = ClosedEvalEnv.Empty
                        setArgsInOrder(continuation.recursorArgs)
                        currentIsWhnf = true
                        continue
                    }
                    rule = continuation.recursor.rules.singleOrNull { it.ctorName == majorHead.name }
                        ?: return fail("recursor rule")
                    if (constructor.numFields != rule.nfields) return fail("recursor fields")
                    val majorArgs = argumentStack.toList()
                    if (majorArgs.size != constructor.numParams + constructor.numFields) {
                        return fail("recursor arity")
                    }
                    fieldArgs = majorArgs.drop(constructor.numParams)
                }
                applyRecursorRule(
                    continuation.recursorConst,
                    continuation.recursor,
                    continuation.recursorArgs,
                    rule,
                    fieldArgs,
                )
            }

            is ClosedEvalContinuation.NatOperand -> {
                val value = terminalNatValue()
                if (value != null) {
                    val values = continuation.values + value
                    val nextIndex = values.size
                    if (nextIndex < continuation.operands.size) {
                        continuations += continuation.copy(values = values)
                        val operand = continuation.operands[nextIndex]
                        setCurrent(operand)
                        setArgsInOrder(argumentsOf(operand))
                        continue
                    }
                    val reduced = continuation.primitive.reduce(values[0], values.getOrNull(1)) { transientNat(it) }
                    if (reduced != null) {
                        currentExpression = reduced
                        currentLocals = ClosedEvalEnv.Empty
                        setArgsInOrder(continuation.extraArgs)
                        continue
                    }
                }
                val definitionValue = continuation.primitiveConst.instantiatedValue()
                currentExpression = definitionValue ?: continuation.primitiveConst
                currentLocals = ClosedEvalEnv.Empty
                setArgsInOrder(continuation.operands + continuation.extraArgs)
                if (definitionValue == null) currentIsWhnf = true
//                else {
//                    deltaReductions += 1
//                    incrementCount(deltaCounts, continuation.primitiveConst.name)
//                }
            }
        }
    }
}

context(env: Environment)
private fun Expression.Const.natPrimitive(): NatPrimitive? {
    if (this.levels.isNotEmpty()) return null
    return when (this.name.toStringDetailed()) {
        "Nat.succ" -> NatPrimitive.Succ
        "Nat.add" -> NatPrimitive.Add
        "Nat.sub" -> NatPrimitive.Sub
        "Nat.mul" -> NatPrimitive.Mul
        "Nat.pow" -> NatPrimitive.Pow
        "Nat.div" -> NatPrimitive.Div
        "Nat.mod" -> NatPrimitive.Mod
        "Nat.beq" -> NatPrimitive.Beq
        "Nat.ble" -> NatPrimitive.Ble
        else -> null
    }
}

context(env: Environment)
private inline fun NatPrimitive.reduce(
    first: NatValue,
    second: NatValue? = null,
    natCtor: (NatValue) -> Expression,
): Expression? {
    val rhs = if (arity == 2) checkNotNull(second) else first
    return when (this) {
        NatPrimitive.Succ -> natCtor(first + NatValue.ONE)
        NatPrimitive.Add -> natCtor(first + rhs)
        NatPrimitive.Sub -> natCtor(if (first >= rhs) first - rhs else NatValue.ZERO)
        NatPrimitive.Mul -> natCtor(first * rhs)
        NatPrimitive.Pow -> {
            val exponent = rhs.toIntOrNull() ?: return null
            natCtor(first.pow(exponent))
        }

        NatPrimitive.Div -> natCtor(first.divLean(rhs))
        NatPrimitive.Mod -> natCtor(first.modLean(rhs))
        NatPrimitive.Beq -> boolCtor(first == rhs)
        NatPrimitive.Ble -> boolCtor(first <= rhs)
    }
}

context(env: Environment)
private fun Expression.Proj.lazyProjectionDefEq(
    other: Expression.Proj,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    var left = this.structExpr.whnfCore(localCtxLeft, cheapProjection = true)
    var right = other.structExpr.whnfCore(localCtxRight, cheapProjection = true)
    val leftHead = left.asAppSpine().first as? Expression.Const
    val rightHead = right.asAppSpine().first as? Expression.Const
    if (leftHead != null && rightHead != null && leftHead.hasSameNameAndLevels(rightHead)) return false
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
    leftCtxId: Int,
    rightCtxId: Int,
): DefEqCacheKey {
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
    val leftCtxId = if (this.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxLeft)
    val rightCtxId = if (other.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxRight)
    if (env.defEqEquivalences.areEquivalent(this.ie, leftCtxId, other.ie, rightCtxId)) return true

    val result = when (this) {
        is Expression.App -> other is Expression.App &&
                this.fnExpr.tryKnownDefEqCongruence(other.fnExpr, localCtxLeft, localCtxRight) &&
                this.argExpr.tryKnownDefEqCongruence(other.argExpr, localCtxLeft, localCtxRight)

        is Expression.Bvar -> other is Expression.Bvar && this.bvar == other.bvar
        is Expression.Const -> other is Expression.Const && this.hasSameNameAndLevels(other)

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
    if (result) env.defEqEquivalences.addEquivalent(this.ie, leftCtxId, other.ie, rightCtxId)
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
        this.rules.forEach { rule ->
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
    val leftConst = leftSpine.first as? Expression.Const
    val rightConst = rightSpine.first as? Expression.Const
    val canReuseBinderKinds = leftConst != null && rightConst != null &&
        leftConst.hasSameNameAndLevels(rightConst)
    var proofArguments: BooleanArray? = null
    var proofArgumentsComputed = false
    var functionType: Expression.ForallE? = null
    val pendingSubst = ArrayDeque<Expression>()

    fun advanceFunctionType(type: Expression.ForallE, argument: Expression): Expression.ForallE {
        pendingSubst.addFirst(argument)
        val directForall = type.bodyExpr as? Expression.ForallE
        if (directForall != null) return directForall
        val nextType = type.bodyExpr.applySubst(pendingSubst)
        pendingSubst.clear()
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
            if (canReuseBinderKinds && !proofArgumentsComputed) {
                proofArguments = leftConst.proofArgumentMask(leftArgs.size)
                proofArgumentsComputed = true
            }
            if (proofArguments?.get(index) == true) {
                env.typedCongruenceProofSkips += 1
                continue
            }
            if (proofArguments != null) {
                if (!leftArgument.isDefEq(rightArgument, localCtxLeft, localCtxRight)) return false
                continue
            }
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
            val domain = functionType.typeExpr
            val domainIsProp = domain.rigidTypeIsProp() ||
                    domain.applySubst(pendingSubst)
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
                if (!left.hasSameNameAndLevels(right)) return null
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
    if (!leftHead.hasSameNameAndLevels(rightHead) || leftSpine.second.size != rightSpine.second.size) return null
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
        !leftHead.hasSameNameAndLevels(rightHead) ||
        leftHints.value != rightHints.value
    ) return null

    val leftCtxId = if (this.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxLeft)
    val rightCtxId = if (other.maxLooseBVarIndex() < 0) 0 else env.localCtxId(localCtxRight)
    val failureKey = this.defEqCacheKey(other, leftCtxId, rightCtxId)
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
            projectionBody = when (val body = projectionBody) {
                is Expression.Mdata -> body.expr
                is Expression.LetE -> body.instantiateLeadingLets()
                is Expression.Lam -> {
                    binderCount += 1
                    body.bodyExpr
                }

                else -> break
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
    if (right == null) return LazyDeltaChoice.Left
    if (left == null) return LazyDeltaChoice.Right

    val kindCmp = left.kind.priority.compareTo(right.kind.priority)
    if (kindCmp > 0) return LazyDeltaChoice.Left
    if (kindCmp < 0) return LazyDeltaChoice.Right

    val heightCmp = left.regularHeight.compareTo(right.regularHeight)
    if (heightCmp > 0) return LazyDeltaChoice.Left
    if (heightCmp < 0) return LazyDeltaChoice.Right
    return LazyDeltaChoice.Both
}

context(env: Environment)
private fun Expression.tryLazyDeltaStep(): LazyDeltaStep? {
    val [headExpr, args] = this.asAppSpine()
    // A projection is not itself a delta target. Keeping it out of the ordinary
    // hint comparison lets the projection-specific paths reduce its structure first.
    if (headExpr is Expression.Proj) return null
    val projectionInfo = (headExpr as? Expression.Const)?.projectionReductionInfo()
    if (projectionInfo != null && args.size < projectionInfo.arity) return null
    return headExpr.lazyDeltaStepInfo(this)
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
private fun Expression.LetE.instantiateLeadingLets(): Expression {
    var tail: Expression = this
    val subst = ArrayDeque<Expression>()
    while (tail is Expression.LetE) {
        subst.addFirst(tail.valueExpr.applySubst(subst))
        tail = tail.bodyExpr
    }
    return tail.applySubst(subst)
}

context(env: Environment)
private fun Expression.reduceBetaLetHead(): Expression {
    var current = this
    while (true) {
        current = when (current) {
            is Expression.Mdata -> current.expr
            is Expression.LetE -> current.instantiateLeadingLets()
            is Expression.App -> {
                val spine = current.unfoldApp()
                when (val head = spine.first) {
                    is Expression.Mdata -> head.expr.applyArgs(spine.second)
                    is Expression.LetE -> head.instantiateLeadingLets().applyArgs(spine.second)

                    is Expression.Lam -> head.applyBetaArgs(spine.second)
                    else -> return current
                }
            }

            else -> return current
        }
    }
}

context(env: Environment)
private fun Expression.applyBetaArgs(args: List<Expression>): Expression {
    var head = this
    var nextArg = 0
    while (true) {
        when (head) {
            is Expression.Mdata -> head = head.expr
            is Expression.LetE -> head = head.instantiateLeadingLets()
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

context(env: Environment)
private fun Expression.lazyDeltaStepInfo(expression: Expression = this): LazyDeltaStep? = when (this) {
    is Expression.Const -> {
        when (val declaration = this.decl) {
            is Declaration.Def -> when (val hints = declaration.hints) {
                Declaration.Def.Hints.Opaque -> LazyDeltaStep(expression, LazyDeltaStepKind.Opaque)
                Declaration.Def.Hints.Abbrev -> LazyDeltaStep(expression, LazyDeltaStepKind.Abbrev)
                is Declaration.Def.Hints.Regular -> LazyDeltaStep(expression, LazyDeltaStepKind.Regular, hints.value)
            }

            is Declaration.Thm -> LazyDeltaStep(expression, LazyDeltaStepKind.Opaque)
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

        is Expression.Const if other is Expression.Const -> this.hasSameNameAndLevels(other)

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
        else -> other is Expression.Lam && this.tryCompareWithFunction(other, localCtxLeft, localCtxRight) ?: false
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
    this.strVal.toUnicodeScalarValues().asReversed().forEach { codePoint ->
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

private class InferRequest(
    val environment: Environment,
    val expression: Expression,
    val localCtx: List<Expression>,
    val validate: Boolean,
)

@IgnorableReturnValue
context(env: Environment)
private fun requireSort(type: Expression, subject: Expression, localCtx: List<Expression>): Level {
    val typeWhnf = type.whnf(localCtx = localCtx)
    val sort = typeWhnf as? Expression.Sort
        ?: error("Expected Sort type for ${subject.toStringDetailed()}, got ${typeWhnf.toStringDetailed()}")
    return sort.level
}

context(env: Environment)
private fun Expression.requireFunctionType(app: Expression.App, localCtx: List<Expression>): Expression.ForallE =
    this.whnf(localCtx = localCtx) as? Expression.ForallE
        ?: error("Expected function type for app ${app.toStringDetailed()}, got ${this.toStringDetailed()}")

context(env: Environment)
private fun Expression.App.checkArgumentType(
    argument: Expression,
    expectedType: Expression,
    inferredType: Expression,
    localCtx: List<Expression>,
) {
//    if (debugTargetDeclaration) {
//        println(
//            "debug argument type: expected=${expectedType.debugHead()} " +
//                    "inferred=${inferredType.debugHead()} argument=${argument.debugHead()}"
//        )
//    }
//    if (
//        debugTargetDeclaration &&
//        (expectedType.debugContainsConstant("Nat.decLe") || inferredType.debugContainsConstant("Nat.decLe"))
//    ) {
//        println(
//            "debug Nat.decLe argument type: expected=${expectedType.debugHead()} " +
//                    "inferred=${inferredType.debugHead()} argument=${argument.debugHead()}"
//        )
//    }
    val previousEagerReduction = env.eagerReduction
    if (argument.isEagerReduceApp()) env.eagerReduction = true
    val matches = try {
        expectedType.isDefEq(inferredType, localCtx, localCtx)
    } finally {
        env.eagerReduction = previousEagerReduction
    }
//    if (debugTargetDeclaration && !matches) {
//        println(
//            "debug mismatch shape: expected=${expectedType.debugShallow()} " +
//                    "inferred=${inferredType.debugShallow()} argument=${argument.debugShallow()}"
//        )
//        println("debug application shape: ${this.debugShallow()}")
//        val pendingConstants = ArrayDeque<Expression>()
//        val seenConstants = mutableSetOf<Int>()
//        pendingConstants.addLast(inferredType)
//        while (pendingConstants.isNotEmpty()) {
//            val expression = pendingConstants.removeLast()
//            if (!seenConstants.add(expression.ie)) continue
//            when (expression) {
//                is Expression.App -> {
//                    pendingConstants.addLast(expression.fnExpr)
//                    pendingConstants.addLast(expression.argExpr)
//                }
//                is Expression.Const -> if (
//                    expression.name.toStringDetailed() == "AbsoluteValue.IsAdmissible.card"
//                ) {
//                    println(
//                        "debug card type=${expression.inferType(validate = false).debugShallow()} " +
//                                "value=${expression.instantiatedValue()?.debugShallow()}"
//                    )
//                    var cardBody = expression.instantiatedValue()
//                    val cardDomains = mutableListOf<String>()
//                    while (cardBody is Expression.Lam) {
//                        cardDomains += cardBody.typeExpr.debugShallow()
//                        cardBody = cardBody.bodyExpr
//                    }
//                    println(
//                        "debug card body: binders=${cardDomains.size} " +
//                                "domains=${cardDomains.joinToString()} tail=${cardBody?.debugShallow()}"
//                    )
//                }
//                is Expression.ForallE -> {
//                    pendingConstants.addLast(expression.typeExpr)
//                    pendingConstants.addLast(expression.bodyExpr)
//                }
//                is Expression.Lam -> {
//                    pendingConstants.addLast(expression.typeExpr)
//                    pendingConstants.addLast(expression.bodyExpr)
//                }
//                is Expression.LetE -> {
//                    pendingConstants.addLast(expression.typeExpr)
//                    pendingConstants.addLast(expression.valueExpr)
//                    pendingConstants.addLast(expression.bodyExpr)
//                }
//                is Expression.Mdata -> pendingConstants.addLast(expression.expr)
//                is Expression.Proj -> pendingConstants.addLast(expression.structExpr)
//                is Expression.Bvar, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> {}
//            }
//        }
//        println(
//            "debug context values: " + localCtx.indices
//                .filter { env.localCtxValue(localCtx, it) != null }
//                .joinToString { index ->
//                    "$index=${env.localCtxValue(localCtx, index)!!.debugShallow()}"
//                }
//        )
//    }
    check(matches) {
        "Application argument type mismatch in app ${this.toStringDetailed()}: " +
                "expected ${expectedType.toStringDetailed()}, got ${inferredType.toStringDetailed()}"
    }
}

context(env: Environment)
fun Expression.inferType(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
    validate: Boolean = true,
): Expression {
    val expression = this.instantiateLevelParams(levelSubst)
    check(expression.isScopedBy(localCtx)) {
        "Inference received an expression outside its context: ${expression.toStringDetailed()}"
    }

    return inferTypeDeep(InferRequest(env, expression, localCtx, validate))
}

private val inferTypeDeep = DeepRecursiveFunction<InferRequest, Expression> { request ->
    val env = request.environment
    context(env) {
        val expr = request.expression
        val contextId = if (expr.maxLooseBVarIndex() < 0) 0 else env.localCtxId(request.localCtx)
        val cacheKey = InferTypeCacheKey(expr.ie, contextId, request.validate)
        val cachedType = env.inferTypeCacheNoLevelSubst[cacheKey]
            ?: if (request.validate) null
            else env.inferTypeCacheNoLevelSubst[cacheKey.copy(validate = true)]

        if (cachedType != null) {
            env.inferTypeCacheHits += 1
            cachedType
        } else {
            val inferredType = when (expr) {
                is Expression.App -> {
                    val [head, arguments] = expr.unfoldApp()
                    var functionType = callRecursive(
                        InferRequest(env, head, request.localCtx, request.validate)
                    ).requireFunctionType(expr, request.localCtx)
                    val pendingSubst = ArrayDeque<Expression>()

                    arguments.forEachIndexed { index, argument ->
                        if (request.validate) {
                            val expectedType = if (pendingSubst.isEmpty()) functionType.typeExpr
                            else functionType.typeExpr.applySubst(pendingSubst)
                            val argumentType = callRecursive(InferRequest(env, argument, request.localCtx, true))
                            expr.checkArgumentType(argument, expectedType, argumentType, request.localCtx)
                        }

                        pendingSubst.addFirst(argument)
                        if (index < arguments.lastIndex) {
                            val body = functionType.bodyExpr
                            if (body is Expression.ForallE) {
                                functionType = body
                            } else {
                                val instantiatedBody = body.applySubst(pendingSubst)
                                functionType = instantiatedBody.requireFunctionType(expr, request.localCtx)
                                pendingSubst.clear()
                            }
                        }
                    }
                    functionType.bodyExpr.applySubst(pendingSubst)
                }

                is Expression.Bvar -> {
                    check(expr.bvar in request.localCtx.indices) {
                        "Unbound bvar ${expr.bvar} in ${expr.toStringDetailed()}"
                    }
                    request.localCtx[expr.bvar].lift(expr.bvar + 1)
                }

                is Expression.Const -> {
                    val type = env.declTypeByName[expr.name] ?: error("Declaration not found for ${expr.name}")
                    type.instantiateLevelParams(expr.composeLevelSubst(emptyMap()))
                }

                is Expression.ForallE -> {
                    val binders = mutableListOf<Pair<Expression.ForallE, List<Expression>>>()
                    var tail: Expression = expr
                    var tailCtx = request.localCtx
                    while (tail is Expression.ForallE) {
                        binders += tail to tailCtx
                        tailCtx = env.consLocalCtx(tail.typeExpr, tailCtx)
                        tail = tail.bodyExpr
                    }

                    val domainSorts = mutableListOf<Level>()
                    binders.forEach { [binder, binderCtx] ->
                        val type = callRecursive(InferRequest(env, binder.typeExpr, binderCtx, request.validate))
                        domainSorts += requireSort(type, binder.typeExpr, binderCtx)
                    }
                    val bodyType = callRecursive(InferRequest(env, tail, tailCtx, request.validate))
                    var level = requireSort(bodyType, tail, tailCtx)
                    domainSorts.asReversed().forEach {
                        level = makeLevelImax(it, level)
                    }
                    env.addCustomExpr { Expression.Sort(level.il, it) }
                }

                is Expression.Lam -> {
                    val binders = mutableListOf<Pair<Expression.Lam, List<Expression>>>()
                    var tail: Expression = expr
                    var tailCtx = request.localCtx
                    while (tail is Expression.Lam) {
                        binders += tail to tailCtx
                        tailCtx = env.consLocalCtx(tail.typeExpr, tailCtx)
                        tail = tail.bodyExpr
                    }

                    if (request.validate) {
                        binders.forEach { [binder, binderCtx] ->
                            val type = callRecursive(InferRequest(env, binder.typeExpr, binderCtx, true))
                            requireSort(type, binder.typeExpr, binderCtx)
                        }
                    }
                    var bodyType = callRecursive(InferRequest(env, tail, tailCtx, request.validate))
                    binders.asReversed().forEach { [binder] ->
                        bodyType = env.addCustomExpr {
                            binder.copyAsForAllE().copy(body = bodyType.ie, ie = it)
                        }
                    }
                    bodyType
                }

                is Expression.Sort -> {
                    val newLevel = env.addCustomSuccLevel(expr.level.il)
                    env.addCustomExpr { Expression.Sort(newLevel.il, it) }
                }

                is Expression.LetE -> {
                    var tail: Expression = expr
                    var tailCtx = request.localCtx
                    val subst = ArrayDeque<Expression>()
                    while (tail is Expression.LetE) {
                        if (request.validate) {
                            val declaredType = callRecursive(InferRequest(env, tail.typeExpr, tailCtx, true))
                            requireSort(declaredType, tail.typeExpr, tailCtx)
                            val valueType = callRecursive(InferRequest(env, tail.valueExpr, tailCtx, true))
                            check(tail.typeExpr.isDefEq(valueType, tailCtx, tailCtx)) {
                                "Let value type mismatch in ${tail.toStringDetailed()}: " +
                                        "expected ${tail.typeExpr.toStringDetailed()}, got ${valueType.toStringDetailed()}"
                            }
                        }
                        subst.addFirst(tail.valueExpr.applySubst(subst))
                        tailCtx = env.consLocalCtx(tail.typeExpr, tailCtx, tail.valueExpr)
                        tail = tail.bodyExpr
                    }
                    callRecursive(InferRequest(env, tail, tailCtx, request.validate)).applySubst(subst)
                }

                is Expression.Mdata -> callRecursive(InferRequest(env, expr.expr, request.localCtx, request.validate))

                is Expression.NatVal -> {
                    val natTypeIndex = env.findRootInductive("Nat")?.first
                        ?: error("Nat literal ${expr.natVal} used without Nat inductive in environment")
                    env.addCustomExpr { Expression.Const(_name = natTypeIndex, us = emptyList(), ie = it) }
                }

                is Expression.Proj -> {
                    val structType = callRecursive(
                        InferRequest(env, expr.structExpr, request.localCtx, request.validate)
                    )
                    expr.inferProjectionType(structType, request.localCtx)
                }

                is Expression.StrVal -> {
                    val stringTypeIndex = env.findRootInductive("String")?.first
                        ?: error("String literal used without String inductive in environment")
                    env.addCustomExpr { Expression.Const(_name = stringTypeIndex, us = emptyList(), ie = it) }
                }
            }
            env.inferTypeCacheNoLevelSubst[cacheKey] = inferredType
            inferredType
        }
    }
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
        val primitive: NatPrimitive,
        val args: List<Expression>,
        val values: List<NatValue>,
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
                    is Expression.LetE -> current = current.instantiateLeadingLets()
                    is Expression.Bvar -> {
                        val value = env.localCtxValue(localCtx, current.bvar)
                        if (value == null) result = current else current = value.lift(current.bvar + 1)
                    }

                    is Expression.Proj -> {
                        frames.addLast(WhnfFrame.ReduceProjection(current, mode))
                        current = current.structExpr
                        if (mode != WhnfMode.CoreCheapProjection) {
                            mode = WhnfMode.Full
                        }
                    }

                    is Expression.App -> {
                        val [headExpr, args] = current.unfoldApp()
                        frames.addLast(WhnfFrame.ApplyHead(current, headExpr, args, mode))
                        current = headExpr
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
                val primitiveSpine = primitiveApp?.unfoldApp()
                val primitive = when (result) {
                    is Expression.Const -> result.natPrimitive()
                    else -> (primitiveSpine?.first as? Expression.Const)?.natPrimitive()
                }
                val primitiveArgs = primitiveSpine?.second
                if (primitiveApp != null && primitive != null && primitiveArgs?.size == primitive.arity) {
                    frames.addLast(
                        WhnfFrame.ReduceNatPrimitive(
                            app = primitiveApp,
                            primitive = primitive,
                            args = primitiveArgs,
                            values = emptyList(),
                            finishFrame = frame,
                        )
                    )
                    current = primitiveArgs.first()
                    mode = WhnfMode.Full
                    result = null
                } else {
                    val unfolded = if (primitive != null) null else result.unfoldValueOnce()
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
                if (value != null) {
                    val values = frame.values + value
                    val nextIndex = values.size
                    if (nextIndex < frame.args.size) {
                        frames.addLast(frame.copy(values = values))
                        current = frame.args[nextIndex]
                        mode = WhnfMode.Full
                        result = null
                        continue
                    }
                    val reduced = frame.primitive.reduce(values[0], values.getOrNull(1)) { value ->
                        env.addCustomExpr { Expression.NatVal(value, it) }
                    }
                    if (reduced != null) {
                        result = reduced
                        frame.finishFrame.original.cacheWhnf(localCtx, result)
                        continue
                    }
                }
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
                    val headDecl = (frame.originalHead as? Expression.Const)?.decl
                    val recursorMajor = (headDecl as? Inductive.RecursorVal)?.let { recursor ->
                        val majorIndex = recursor.numParams + recursor.numMotives + recursor.numMinors + recursor.numIndices
                        frame.args.getOrNull(majorIndex)
                    }
                    val quotMajor = if (
                        recursorMajor == null && headDecl is Declaration.Quot &&
                        (headDecl.kind == Declaration.Quot.Kind.Lift || headDecl.kind == Declaration.Quot.Kind.Ind)
                    ) {
                        val arity = headDecl.typeExpr.forallBinderCount()
                        if (frame.args.size < arity) null else frame.args[arity - 1]
                    } else null
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
    val result = normalizedExpr.tryRecognizeNatLiteralCore(localCtx)
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
            is Expression.LetE -> current = current.instantiateLeadingLets()
            else -> {
                val baseValue = current.asNatLiteralValue()
                if (baseValue != null) return baseValue + succOffset

                val appExpr = current as? Expression.App ?: return null
                val [headExpr, args] = appExpr.unfoldApp()
                val headConst = headExpr as? Expression.Const ?: return null
                val primitive = headConst.natPrimitive() ?: return null

                fun natArg(index: Int): NatValue? = args.getOrNull(index)?.tryRecognizeNatLiteral(emptyMap(), localCtx)

                when (primitive) {
                    NatPrimitive.Succ -> {
                        current = args.getOrNull(0) ?: return null
                        succOffset += NatValue.ONE
                        continue
                    }

                    NatPrimitive.Beq, NatPrimitive.Ble -> return null
                    else -> {
                        val first = natArg(0) ?: return null
                        val second = natArg(1) ?: return null
                        val reduced = primitive.reduce(first, second) { Expression.NatVal(it, Int.MIN_VALUE) }
                                as? Expression.NatVal ?: return null
                        return reduced.natVal + succOffset
                    }
                }
            }
        }
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
    val primitive = headConst.natPrimitive() ?: return null

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

    val first = natArg(0) ?: return null
    val second = if (primitive.arity == 2) natArg(1) ?: return null else null
    return primitive.reduce(first, second) { value ->
        env.addCustomExpr { Expression.NatVal(value, it) }
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
    val pendingSubst = ArrayDeque<Expression>()
    repeat(constructorDecl.numParams + this.projIndex) { binderIndex ->
        val ctorForall = ctorType as? Expression.ForallE
            ?: error("Constructor ${constructorDecl.name} has too few binders while checking projection ${this.toStringDetailed()}")
        if (isPropStructure && binderIndex >= constructorDecl.numParams) {
            val priorFieldIndex = binderIndex - constructorDecl.numParams
            val priorFieldType = ctorForall.typeExpr.applySubst(pendingSubst)
            val priorFieldSort = priorFieldType.inferSort(localCtx = localCtx, validate = false)
            if (!priorFieldSort.isLessOrEqual(Level.Zero)) {
                nonPropFieldIndices += priorFieldIndex
            } else {
                check(!priorFieldType.containsProjectionOf(this.typeNameExpr, nonPropFieldIndices)) {
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
        pendingSubst.addFirst(binderArg)
        ctorType = ctorForall.bodyExpr
        if (ctorType !is Expression.ForallE) {
            ctorType = ctorType.applySubst(pendingSubst)
            pendingSubst.clear()
        }
    }

    val targetFieldBinder = ctorType as? Expression.ForallE
        ?: error("Constructor ${constructorDecl.name} has too few fields for projection ${this.toStringDetailed()}")
    val projectedType = targetFieldBinder.typeExpr.applySubst(pendingSubst)
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
private fun Expression.containsProjectionOf(typeName: Name, projIndices: Set<Int>): Boolean = when (this) {
    else if projIndices.isEmpty() -> false
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
                Expression.Proj(typeName = inductiveDeclIndex, idx = fieldIndex, struct = majorWhnf.ie, ie = it)
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
        repeat(constructor.numFields) { fieldIndex ->
            val projection = env.addCustomExpr {
                Expression.Proj(typeName = inductiveIndex, idx = fieldIndex, struct = value.ie, ie = it)
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
    return constructor.numFields == 0 && leftType.isDefEq(
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

private data class PostorderFrame(val expression: Expression, val expanded: Boolean)

context(env: Environment)
private inline fun Expression.evaluatePostorder(
    isEvaluated: (Expression) -> Boolean,
    evaluate: (Expression) -> Unit,
) {
    val stack = ArrayDeque<PostorderFrame>()
    stack.add(PostorderFrame(this, false))
    while (stack.isNotEmpty()) {
        val (expression, expanded) = stack.removeLast()
        if (isEvaluated(expression)) continue
        if (expanded) {
            evaluate(expression)
            continue
        }

        stack.add(PostorderFrame(expression, true))
        when (expression) {
            is Expression.App -> {
                stack.add(PostorderFrame(expression.fnExpr, false))
                stack.add(PostorderFrame(expression.argExpr, false))
            }

            is Expression.ForallE -> {
                stack.add(PostorderFrame(expression.typeExpr, false))
                stack.add(PostorderFrame(expression.bodyExpr, false))
            }

            is Expression.Lam -> {
                stack.add(PostorderFrame(expression.typeExpr, false))
                stack.add(PostorderFrame(expression.bodyExpr, false))
            }

            is Expression.LetE -> {
                stack.add(PostorderFrame(expression.typeExpr, false))
                stack.add(PostorderFrame(expression.valueExpr, false))
                stack.add(PostorderFrame(expression.bodyExpr, false))
            }

            is Expression.Mdata -> stack.add(PostorderFrame(expression.expr, false))
            is Expression.Proj -> stack.add(PostorderFrame(expression.structExpr, false))
            is Expression.Bvar,
            is Expression.Const,
            is Expression.NatVal,
            is Expression.Sort,
            is Expression.StrVal -> {}
        }
    }
}

fun Expression.maxLooseBVarIndex(): Int {
    check(looseBVarRange >= 0) { "Expression $ie has not been registered" }
    return looseBVarRange - 1
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
    val cacheKey = InstantiateLevelParamsCacheKey(
        this.ie,
        subst.entries.map { entry -> entry.key to entry.value.il }.sortedBy { it.first },
    )
    env.instantiateLevelParamsCache[cacheKey]?.let { return it }

    val cache = mutableMapOf<Int, Expression>()
    this.evaluatePostorder(
        isEvaluated = { cache[it.ie] != null },
    ) { expr ->
        val result = when (expr) {
            is Expression.Bvar, is Expression.NatVal, is Expression.StrVal -> expr
            is Expression.Sort -> {
                val level = expr.level
                val newLevel = level.instantiateLevelParams(subst)
                if (newLevel == level) expr else env.addCustomExpr { expr.copy(sort = newLevel.il, ie = it) }
            }

            is Expression.Const -> {
                val levels = expr.levels
                val newLevels = levels.map { it.instantiateLevelParams(subst) }
                if (newLevels.indices.all { newLevels[it].il == levels[it].il }) expr
                else env.addCustomExpr { expr.copy(us = newLevels.map { it.il }, ie = it) }
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
    return (cache[this.ie] ?: this).also { result ->
        env.instantiateLevelParamsCache[cacheKey] = result
    }
}

context(env: Environment)
fun Expression.applySubst(subst: List<Expression>): Expression {
    if (subst.isEmpty() || this.maxLooseBVarIndex() < 0) return this
    val singleSubstKey = subst.singleOrNull()?.let { ExprPairKey(this.ie, it.ie) }
    if (singleSubstKey != null) {
        env.applySubstSingleCache[singleSubstKey]?.let { return it }
    }
    val multiSubstKey = if (subst.size > 1) {
        ApplySubstCacheKey(this.ie, subst.map { it.ie })
    } else {
        null
    }
    if (multiSubstKey != null) {
        env.applySubstCache[multiSubstKey]?.let { return it }
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
    if (multiSubstKey != null) env.applySubstCache[multiSubstKey] = result
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
    private var expressions: Array<Expression?> = arrayOfNulls(16)
    private var depths = IntArray(16)
    private var states = ByteArray(16)
    private var firstResults: Array<Expression?> = arrayOfNulls(16)
    private var secondResults: Array<Expression?> = arrayOfNulls(16)
    private var size = 0

    fun add(expr: Expression, depth: Int) {
        if (size == expressions.size) {
            expressions = expressions.copyOf(size * 2)
            depths = depths.copyOf(size * 2)
            states = states.copyOf(size * 2)
            firstResults = firstResults.copyOf(size * 2)
            secondResults = secondResults.copyOf(size * 2)
        }
        expressions[size] = expr
        depths[size] = depth
        states[size] = 0
        size++
    }

    fun lastIndex(): Int {
        check(size > 0)
        return size - 1
    }

    fun expressionAt(index: Int): Expression = expressions[index]!!
    fun depthAt(index: Int): Int = depths[index]
    fun stateAt(index: Int): Int = states[index].toInt()
    fun setState(index: Int, state: Int) {
        states[index] = state.toByte()
    }

    fun firstResultAt(index: Int): Expression = firstResults[index]!!
    fun setFirstResult(index: Int, result: Expression) {
        firstResults[index] = result
    }

    fun secondResultAt(index: Int): Expression = secondResults[index]!!
    fun setSecondResult(index: Int, result: Expression) {
        secondResults[index] = result
    }

    fun removeLast() {
        val index = lastIndex()
        expressions[index] = null
        firstResults[index] = null
        secondResults[index] = null
        size--
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

    val stack = BinderRewriteStack()
    stack.add(this, depth)
    var result: Expression = this
    while (stack.isNotEmpty()) {
        val stackIndex = stack.lastIndex()
        val expr = stack.expressionAt(stackIndex)
        val currentDepth = stack.depthAt(stackIndex)
        val state = stack.stateAt(stackIndex)
        if (state == 0 && expr.maxLooseBVarIndex() < currentDepth) {
            result = expr
            stack.removeLast()
            continue
        }
        val useCache = env.expressionIsShared(expr.ie)
        val key = if (useCache) cacheKey(expr, currentDepth) else 0L
        when (state) {
            0 -> {
                val cached = if (useCache) cache[key] else null
                if (cached != null) {
                    result = cached
                    stack.removeLast()
                    continue
                }
                when (expr) {
                    is Expression.Bvar -> {
                        result = rewriteBvar(expr, currentDepth)
                        if (useCache) cache[key] = result
                        stack.removeLast()
                    }

                    is Expression.App -> {
                        stack.setState(stackIndex, 1)
                        stack.add(expr.fnExpr, currentDepth)
                    }

                    is Expression.ForallE -> {
                        stack.setState(stackIndex, 1)
                        stack.add(expr.typeExpr, currentDepth)
                    }

                    is Expression.Lam -> {
                        stack.setState(stackIndex, 1)
                        stack.add(expr.typeExpr, currentDepth)
                    }

                    is Expression.LetE -> {
                        stack.setState(stackIndex, 1)
                        stack.add(expr.typeExpr, currentDepth)
                    }

                    is Expression.Mdata -> {
                        stack.setState(stackIndex, 1)
                        stack.add(expr.expr, currentDepth)
                    }

                    is Expression.Proj -> {
                        stack.setState(stackIndex, 1)
                        stack.add(expr.structExpr, currentDepth)
                    }

                    else -> error("Unexpected open expression $expr")
                }
            }

            1 -> when (expr) {
                is Expression.Mdata -> {
                    result = if (result === expr.expr) expr
                    else env.addCustomExpr { expr.copy(_expr = result.ie, ie = it) }
                    if (useCache) cache[key] = result
                    stack.removeLast()
                }

                is Expression.Proj -> {
                    result = if (result === expr.structExpr) expr
                    else env.addCustomExpr { expr.copy(struct = result.ie, ie = it) }
                    if (useCache) cache[key] = result
                    stack.removeLast()
                }

                is Expression.App -> {
                    stack.setFirstResult(stackIndex, result)
                    stack.setState(stackIndex, 2)
                    stack.add(expr.argExpr, currentDepth)
                }

                is Expression.ForallE -> {
                    stack.setFirstResult(stackIndex, result)
                    stack.setState(stackIndex, 2)
                    stack.add(expr.bodyExpr, currentDepth + 1)
                }

                is Expression.Lam -> {
                    stack.setFirstResult(stackIndex, result)
                    stack.setState(stackIndex, 2)
                    stack.add(expr.bodyExpr, currentDepth + 1)
                }

                is Expression.LetE -> {
                    stack.setFirstResult(stackIndex, result)
                    stack.setState(stackIndex, 2)
                    stack.add(expr.valueExpr, currentDepth)
                }

                else -> error("Unexpected rewrite state for $expr")
            }

            2 -> {
                val firstResult = stack.firstResultAt(stackIndex)
                when (expr) {
                    is Expression.App -> {
                        result = if (firstResult === expr.fnExpr && result === expr.argExpr) expr
                        else env.addCustomExpr { expr.copy(fn = firstResult.ie, arg = result.ie, ie = it) }
                        if (useCache) cache[key] = result
                        stack.removeLast()
                    }

                    is Expression.ForallE -> {
                        result = if (firstResult === expr.typeExpr && result === expr.bodyExpr) expr
                        else env.addCustomExpr { expr.copy(type = firstResult.ie, body = result.ie, ie = it) }
                        if (useCache) cache[key] = result
                        stack.removeLast()
                    }

                    is Expression.Lam -> {
                        result = if (firstResult === expr.typeExpr && result === expr.bodyExpr) expr
                        else env.addCustomExpr { expr.copy(type = firstResult.ie, body = result.ie, ie = it) }
                        if (useCache) cache[key] = result
                        stack.removeLast()
                    }

                    is Expression.LetE -> {
                        stack.setSecondResult(stackIndex, result)
                        stack.setState(stackIndex, 3)
                        stack.add(expr.bodyExpr, currentDepth + 1)
                    }

                    else -> error("Unexpected rewrite state for $expr")
                }
            }

            3 -> {
                check(expr is Expression.LetE)
                val newType = stack.firstResultAt(stackIndex)
                val newValue = stack.secondResultAt(stackIndex)
                result = if (
                    newType === expr.typeExpr &&
                    newValue === expr.valueExpr &&
                    result === expr.bodyExpr
                ) {
                    expr
                } else {
                    env.addCustomExpr {
                        expr.copy(
                            type = newType.ie,
                            value = newValue.ie,
                            body = result.ie,
                            ie = it,
                        )
                    }
                }
                if (useCache) cache[key] = result
                stack.removeLast()
            }

            else -> error("Unexpected binder rewrite state")
        }
    }
    return result
}

context(env: Environment)
fun Level.instantiateLevelParams(subst: Map<Int, Level>): Level {
    return when (this) {
        Level.Zero -> this
        is Level.Param -> subst[this.il] ?: this

        is Level.Succ -> {
            val level = this.level
            val newLevel = level.instantiateLevelParams(subst)
            if (newLevel == level) this else env.addCustomSuccLevel(newLevel.il)
        }

        is Level.Max -> {
            val left = this.left
            val right = this.right
            val newLeft = left.instantiateLevelParams(subst)
            val newRight = right.instantiateLevelParams(subst)
            if (newLeft == left && newRight == right) this else makeLevelMax(newLeft, newRight)
        }

        is Level.Imax -> {
            val left = this.left
            val right = this.right
            val newLeft = left.instantiateLevelParams(subst)
            val newRight = right.instantiateLevelParams(subst)
            if (newLeft == left && newRight == right) this else makeLevelImax(newLeft, newRight)
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
    val params = this.decl.levelParams
    check(params.size == this.levels.size) {
        "Universe argument mismatch for ${this.toStringDetailed()}: expected ${params.size}, got ${this.levels.size}"
    }
    return params.indices.associate { index ->
        val level = this.levels[index]
        params[index].il to if (outer.isEmpty()) level else level.instantiateLevelParams(outer)
    }
}
