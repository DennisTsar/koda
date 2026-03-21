package io.github.opletter.koda

fun typeCheck(data: List<ExportType>) {
    val env = Environment()
//    typeCheck(data, env = env)
    context(env) {
        _typeCheck(data)
    }
}

context(env: Environment)
fun _typeCheck(rawData: List<ExportType>) {
    rawData.forEach { data ->
        println(data)
        println("---")
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

                when (data) {
                    is Declaration.Axiom -> {} // no extra checks needed
                    is Declaration.Def -> {
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for $data"
                        }
                    }

                    is Declaration.Opaque -> {
                        // TODO: treat opqaue differently
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for $data"
                        }
                    }

                    is Declaration.Quot -> {} // no extra checks needed
                    is Declaration.Thm -> {
//                        if (data.typeExpr.ie == 70618) {
//                            env.shouldLog = true
//                        }
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for $data"
                        }
                        check(declaredTypeSortLevel.isLessOrEqual(Level.Zero)) {
                            "The type of a theorem has to be a proposition: found ${data.typeExpr.toStringDetailed()}"
                        }
                    }
                }

                env.declTypeByName[data.name] = data.typeExpr

                // (4): "the declaration's type has no free variables"
                // TODO
            }

            is Inductive -> {
                checkInductive(data)
            }

            is Meta -> {} // no-op
        }
        env.clearCustom()
//        println("apple: ${env.levels.size} // ${env.expressions.size} // ${env.declarations.size} // ${env.names.size}")
    }
}


context(env: Environment)
fun typeCheckDeclaration(value: Expression, expectedType: Expression): Boolean {
    if (env.shouldLog) println("found value: ${value.toStringDetailed()}")
    val inferredValueType = value.inferType()
    if (env.shouldLog) println("inferred type of value: ${inferredValueType.expr.toStringDetailed()}")
    val actualType = inferredValueType.expr
    // made it to: Def(_name=2098, _levelParams=[22, 6], type=12166, value=12236, hints=Abbrev, safety=Safe, all=[2098])
    // before Java heap space error, ran for 1 min 21 sec
//    return Blah.isDefEq(Everything(env, expectedType, actualType, levelSubstRight = inferredValueType.levelSubst))
    // made it to: Def(_name=1944, _levelParams=[6], type=10830, value=10837, hints=Abbrev, safety=Safe, all=[1944])
    // before stack overflow, ran for 30 sec
    return expectedType.isDefEq(actualType, levelSubstRight = inferredValueType.levelSubst)
}

class Everything(
    val env: Environment,
    val _this: Expression,
    val other: Expression,
    val levelSubstLeft: Map<Int, Level> = emptyMap(),
    val levelSubstRight: Map<Int, Level> = emptyMap(),
    val localCtxLeft: List<Expression> = emptyList(),
    val localCtxRight: List<Expression> = emptyList(),
)

object Blah {
    val isDefEq: DeepRecursiveFunction<Everything, Boolean> = DeepRecursiveFunction { t ->
        context(t.env) {
            val (env, _this, other, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight) = t
            val lhsWhnf = _this.reduce(levelSubst = levelSubstLeft)
            val rhsWhnf = other.reduce(levelSubst = levelSubstRight)
            isDefEqWhnf.callRecursive(
                Everything(
                    env,
                    lhsWhnf.expr,
                    rhsWhnf.expr,
                    lhsWhnf.levelSubst,
                    rhsWhnf.levelSubst,
                    localCtxLeft,
                    localCtxRight,
                )
            )
        }
    }
    val isDefEqWhnf: DeepRecursiveFunction<Everything, Boolean> = DeepRecursiveFunction { t ->
        val (env, _this, other, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight) = t
        context(t.env) {
            when (_this) {
                is Expression.App if other is Expression.App ->
                    isDefEq.callRecursive(
                        Everything(
                            env,
                            _this.fnExpr,
                            other.fnExpr,
                            levelSubstLeft,
                            levelSubstRight,
                            localCtxLeft,
                            localCtxRight
                        )
                    ) &&
                            isDefEq.callRecursive(
                                Everything(
                                    env,
                                    _this.argExpr,
                                    other.argExpr,
                                    levelSubstLeft,
                                    levelSubstRight,
                                    localCtxLeft,
                                    localCtxRight
                                )
                            )

                is Expression.Bvar if other is Expression.Bvar -> {
                    if (_this.bvar == other.bvar) {
                        true
                    } else if (_this.bvar < localCtxLeft.size && other.bvar < localCtxRight.size) {
                        val thisType = localCtxLeft[_this.bvar].lift(_this.bvar + 1)
                        val otherType = localCtxRight[other.bvar].lift(other.bvar + 1)
                        val typesDefEq = isDefEq.callRecursive(
                            Everything(
                                env, thisType,
                                otherType,
                                levelSubstLeft,
                                levelSubstRight,
                                localCtxLeft,
                                localCtxRight,
                            )
                        )
                        if (!typesDefEq) {
                            false
                        } else {
                            val thisSort = thisType.inferSort(levelSubstLeft, localCtxLeft)
                            val otherSort = otherType.inferSort(levelSubstRight, localCtxRight)
                            (thisSort.isLessOrEqual(Level.Zero) && otherSort.isLessOrEqual(Level.Zero))
                                    || _this.tryStructureEtaDefEq(
                                other,
                                levelSubstLeft,
                                levelSubstRight,
                                localCtxLeft,
                                localCtxRight,
                            )
                        }
                    } else {
                        false
                    }
                }

                is Expression.Const if other is Expression.Const ->
                    _this.name == other.name &&
                            _this.levels.size == other.levels.size &&
                            _this.levels.zip(other.levels).all { [l1, l2] ->
                                l1.instantiateLevelParams(levelSubstLeft)
                                    .isEqual(l2.instantiateLevelParams(levelSubstRight))
                            }

                is Expression.ForallE if other is Expression.ForallE -> {
                    isDefEq.callRecursive(
                        Everything(
                            env,
                            _this.typeExpr,
                            other.typeExpr,
                            levelSubstLeft,
                            levelSubstRight,
                            localCtxLeft,
                            localCtxRight
                        )
                    ) &&
                            isDefEq.callRecursive(
                                Everything(
                                    env, _this.bodyExpr,
                                    other.bodyExpr,
                                    levelSubstLeft,
                                    levelSubstRight,
                                    listOf(_this.typeExpr) + localCtxLeft,
                                    listOf(other.typeExpr) + localCtxRight,
                                )
                            )
                }

                is Expression.Lam if other is Expression.Lam -> {
                    isDefEq.callRecursive(
                        Everything(
                            env,
                            _this.typeExpr,
                            other.typeExpr,
                            levelSubstLeft,
                            levelSubstRight,
                            localCtxLeft,
                            localCtxRight
                        )
                    ) &&
                            isDefEq.callRecursive(
                                Everything(
                                    env, _this.bodyExpr,
                                    other.bodyExpr,
                                    levelSubstLeft,
                                    levelSubstRight,
                                    listOf(_this.typeExpr) + localCtxLeft,
                                    listOf(other.typeExpr) + localCtxRight,
                                )
                            )
                }

                is Expression.Lam ->
                    _this.tryEtaReduce()
                        ?.let {
                            isDefEq.callRecursive(
                                Everything(
                                    env,
                                    it,
                                    other,
                                    levelSubstLeft,
                                    levelSubstRight,
                                    localCtxLeft,
                                    localCtxRight
                                )
                            )
                        }
                        ?: false

                is Expression.LetE if other is Expression.LetE -> TODO()
                is Expression.Mdata if other is Expression.Mdata -> TODO()
                is Expression.NatVal if other is Expression.NatVal -> _this.natVal == other.natVal
                is Expression.Proj if other is Expression.Proj ->
                    _this.typeNameExpr == other.typeNameExpr &&
                            _this.projIndex == other.projIndex &&
                            isDefEq.callRecursive(
                                Everything(
                                    env, _this.structExpr,
                                    other.structExpr,
                                    levelSubstLeft,
                                    levelSubstRight,
                                    localCtxLeft,
                                    localCtxRight
                                )
                            )

                is Expression.Sort if other is Expression.Sort ->
                    _this.level.instantiateLevelParams(levelSubstLeft)
                        .isEqual(other.level.instantiateLevelParams(levelSubstRight))

                is Expression.StrVal if other is Expression.StrVal -> _this.strVal == other.strVal
                else -> {
                    if (other is Expression.Lam) {
                        other.tryEtaReduce()?.let {
                            return@DeepRecursiveFunction isDefEq.callRecursive(
                                Everything(
                                    env,
                                    _this,
                                    it,
                                    levelSubstLeft,
                                    levelSubstRight,
                                    localCtxLeft,
                                    localCtxRight
                                )
                            )
                        }
                    }
                    if (_this.tryStructureEtaDefEq(
                            other,
                            levelSubstLeft,
                            levelSubstRight,
                            localCtxLeft,
                            localCtxRight
                        )
                    ) {
                        return@DeepRecursiveFunction true
                    }
                    val reducedThis = _this.reduce(levelSubstLeft)
                    val reducedOther = other.reduce(levelSubstRight)
                    if (reducedThis.expr == _this && reducedOther.expr == other) {
                        false
                    } else {
                        isDefEq.callRecursive(
                            Everything(
                                env, reducedThis.expr,
                                reducedOther.expr,
                                reducedThis.levelSubst,
                                reducedOther.levelSubst,
                                localCtxLeft,
                                localCtxRight,
                            )
                        )
                    }
                }
            }
        }
    }
}

context(env: Environment)
fun Expression.isDefEq(
    other: Expression,
    levelSubstLeft: Map<Int, Level> = emptyMap(),
    levelSubstRight: Map<Int, Level> = emptyMap(),
    localCtxLeft: List<Expression> = emptyList(),
    localCtxRight: List<Expression> = emptyList(),
): Boolean {
    if (this == other) return true
    if (this.sameShape(other)) return true
    if (env.shouldLog) {
        println("comparing:\n$this\n$other")
    }
    val lhsWhnf = this.reduce(levelSubst = levelSubstLeft)
    val rhsWhnf = other.reduce(levelSubst = levelSubstRight)
    return lhsWhnf.expr.isDefEqWhnf(
        rhsWhnf.expr,
        lhsWhnf.levelSubst,
        rhsWhnf.levelSubst,
        localCtxLeft,
        localCtxRight,
    )
}

context(env: Environment)
private fun Expression.sameShape(other: Expression): Boolean {
    return when (this) {
        is Expression.Bvar if other is Expression.Bvar -> this.bvar == other.bvar
        is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
        is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
        is Expression.Sort if other is Expression.Sort -> this.level.sameShape(other.level)
        is Expression.Const if other is Expression.Const ->
            this.name == other.name &&
                    this.levels.size == other.levels.size &&
                    this.levels.zip(other.levels).all { it.first.sameShape(it.second) }

        is Expression.App if other is Expression.App ->
            this.fnExpr.sameShape(other.fnExpr) && this.argExpr.sameShape(other.argExpr)

        is Expression.ForallE if other is Expression.ForallE ->
            this.typeExpr.sameShape(other.typeExpr) && this.bodyExpr.sameShape(other.bodyExpr)

        is Expression.Lam if other is Expression.Lam ->
            this.typeExpr.sameShape(other.typeExpr) && this.bodyExpr.sameShape(other.bodyExpr)

        is Expression.LetE if other is Expression.LetE ->
            this.typeExpr.sameShape(other.typeExpr) &&
                    this.valueExpr.sameShape(other.valueExpr) &&
                    this.bodyExpr.sameShape(other.bodyExpr)

        is Expression.Mdata if other is Expression.Mdata ->
            this.expr.sameShape(other.expr)

        is Expression.Proj if other is Expression.Proj ->
            this.typeNameExpr == other.typeNameExpr &&
                    this.projIndex == other.projIndex &&
                    this.structExpr.sameShape(other.structExpr)

        else -> false
    }
}

context(env: Environment)
private fun Expression.isDefEqWhnf(
    other: Expression,
    levelSubstLeft: Map<Int, Level>,
    levelSubstRight: Map<Int, Level>,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    return when (this) {
        is Expression.App if other is Expression.App -> {
            val lhsNat = this.tryUnfoldNatSuccChain()
            val rhsNat = other.tryUnfoldNatSuccChain()
            if (lhsNat != null && rhsNat != null && lhsNat.count == rhsNat.count) {
                lhsNat.base.isDefEq(
                    rhsNat.base,
                    levelSubstLeft,
                    levelSubstRight,
                    localCtxLeft,
                    localCtxRight
                )
            } else {
                this.fnExpr.isDefEq(other.fnExpr, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight) &&
                        this.argExpr.isDefEq(
                            other.argExpr,
                            levelSubstLeft,
                            levelSubstRight,
                            localCtxLeft,
                            localCtxRight
                        )
            }
        }

        is Expression.App if other is Expression.NatVal ->
            this.tryUnfoldNatSuccChain()
                ?.let { chain ->
                    other.tryCompareWithNatSuccChain(
                        chain,
                        chainLevelSubst = levelSubstLeft,
                        natLevelSubst = levelSubstRight,
                        chainLocalCtx = localCtxLeft,
                        natLocalCtx = localCtxRight,
                    )
                }
                ?: false

        is Expression.Bvar if other is Expression.Bvar -> {
            if (this.bvar == other.bvar) {
                true
            } else if (this.bvar < localCtxLeft.size && other.bvar < localCtxRight.size) {
                val thisType = localCtxLeft[this.bvar].lift(this.bvar + 1)
                val otherType = localCtxRight[other.bvar].lift(other.bvar + 1)
                val typesDefEq = thisType.isDefEq(
                    otherType,
                    levelSubstLeft,
                    levelSubstRight,
                    localCtxLeft,
                    localCtxRight,
                )
                if (!typesDefEq) {
                    false
                } else {
                    val thisSort = thisType.inferSort(levelSubstLeft, localCtxLeft)
                    val otherSort = otherType.inferSort(levelSubstRight, localCtxRight)
                    (thisSort.isLessOrEqual(Level.Zero) && otherSort.isLessOrEqual(Level.Zero))
                            || this.tryStructureEtaDefEq(
                        other,
                        levelSubstLeft,
                        levelSubstRight,
                        localCtxLeft,
                        localCtxRight,
                    )
                }
            } else {
                false
            }
        }

        is Expression.Const if other is Expression.Const ->
            if (this.name != other.name || this.levels.size != other.levels.size) {
                false
            } else {
                this.levels.zip(other.levels).all { [l1, l2] ->
                    val leftLevel = l1.instantiateLevelParams(levelSubstLeft)
                    val rightLevel = l2.instantiateLevelParams(levelSubstRight)
                    val standardResult = leftLevel.sameShape(rightLevel) || leftLevel.isEqual(rightLevel)
                    if (standardResult) {
                        true
                    } else {
                        val shouldTrySelfRefFallback =
                            l1.hasNestedSelfReferentialParam(levelSubstLeft) ||
                                    l2.hasNestedSelfReferentialParam(levelSubstRight)
                        if (!shouldTrySelfRefFallback) {
                            false
                        } else {
                            val leftFallback = l1.instantiateLevelParamsForConstEq(levelSubstLeft)
                            val rightFallback = l2.instantiateLevelParamsForConstEq(levelSubstRight)
                            leftFallback.sameShape(rightFallback) || leftFallback.isEqual(rightFallback)
                        }
                    }
                }
            }

        is Expression.ForallE if other is Expression.ForallE -> {
            this.typeExpr.isDefEq(other.typeExpr, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight) &&
                    this.bodyExpr.isDefEq(
                        other.bodyExpr,
                        levelSubstLeft,
                        levelSubstRight,
                        listOf(this.typeExpr) + localCtxLeft,
                        listOf(other.typeExpr) + localCtxRight,
                    )
        }

        is Expression.Lam if other is Expression.Lam -> {
            this.typeExpr.isDefEq(other.typeExpr, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight) &&
                    this.bodyExpr.isDefEq(
                        other.bodyExpr,
                        levelSubstLeft,
                        levelSubstRight,
                        listOf(this.typeExpr) + localCtxLeft,
                        listOf(other.typeExpr) + localCtxRight,
                    )
        }

        is Expression.Lam ->
            this.tryEtaReduce()?.isDefEq(other, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight) ?: false

        is Expression.LetE if other is Expression.LetE -> TODO()
        is Expression.Mdata if other is Expression.Mdata -> TODO()
        is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
        is Expression.NatVal if other is Expression.App ->
            other.tryUnfoldNatSuccChain()
                ?.let { chain ->
                    this.tryCompareWithNatSuccChain(
                        chain,
                        chainLevelSubst = levelSubstRight,
                        natLevelSubst = levelSubstLeft,
                        chainLocalCtx = localCtxRight,
                        natLocalCtx = localCtxLeft,
                    )
                }
                ?: false
        is Expression.Proj if other is Expression.Proj ->
            this.typeNameExpr == other.typeNameExpr &&
                    this.projIndex == other.projIndex &&
                    this.structExpr.isDefEq(
                        other.structExpr,
                        levelSubstLeft,
                        levelSubstRight,
                        localCtxLeft,
                        localCtxRight
                    )

        is Expression.Sort if other is Expression.Sort ->
            this.level.instantiateLevelParams(levelSubstLeft)
                .isEqual(other.level.instantiateLevelParams(levelSubstRight))

        is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
        else -> {
            if (other is Expression.Lam) {
                other.tryEtaReduce()?.let {
                    return this.isDefEq(it, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight)
                }
            }
            if (this.tryStructureEtaDefEq(other, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight)) {
                return true
            }
            val reducedThis = this.reduce(levelSubstLeft)
            val reducedOther = other.reduce(levelSubstRight)
            if (reducedThis.expr == this && reducedOther.expr == other) {
                false
            } else {
                reducedThis.expr.isDefEq(
                    reducedOther.expr,
                    reducedThis.levelSubst,
                    reducedOther.levelSubst,
                    localCtxLeft,
                    localCtxRight,
                )
            }
        }
    }
}

private data class NatSuccChain(
    val count: Long,
    val base: Expression,
)

private const val MAX_NAT_LITERAL_RECURSOR_REDUCTION = 1L

context(env: Environment)
private fun Expression.tryUnfoldNatSuccChain(): NatSuccChain? {
    var current: Expression = this
    var succCount = 0L

    while (true) {
        val app = current as? Expression.App ?: break
        val fnConst = app.fnExpr as? Expression.Const ?: break
        val ctorDecl = fnConst.decl as? Inductive.ConstructorVal ?: break
        val inductiveName = ctorDecl.inductName as? Name.Str ?: break
        if (inductiveName.pre != 0 || inductiveName.str != "Nat") break
        if (ctorDecl.numParams != 0 || ctorDecl.numFields != 1) break

        succCount += 1
        current = app.argExpr
    }

    return if (succCount == 0L) null else NatSuccChain(succCount, current)
}

context(env: Environment)
private fun Expression.NatVal.tryCompareWithNatSuccChain(
    chain: NatSuccChain,
    chainLevelSubst: Map<Int, Level>,
    natLevelSubst: Map<Int, Level>,
    chainLocalCtx: List<Expression>,
    natLocalCtx: List<Expression>,
): Boolean {
    if (this.natVal < chain.count) return false
    val remaining = this.natVal - chain.count
    val baseExpr = chain.base
    return when {
        baseExpr is Expression.NatVal -> baseExpr.natVal == remaining
        baseExpr.isNatZeroCtorConst() -> remaining == 0L
        else -> {
            val remainingExpr = env.addCustomExpr { Expression.NatVal(remaining, it) }
            baseExpr.isDefEq(remainingExpr, chainLevelSubst, natLevelSubst, chainLocalCtx, natLocalCtx)
        }
    }
}

context(env: Environment)
private fun Expression.isNatZeroCtorConst(): Boolean {
    val constExpr = this as? Expression.Const ?: return false
    val ctorDecl = constExpr.decl as? Inductive.ConstructorVal ?: return false
    if (ctorDecl.numParams != 0 || ctorDecl.numFields != 0) return false
    val inductiveName = ctorDecl.inductName as? Name.Str ?: return false
    return inductiveName.pre == 0 && inductiveName.str == "Nat"
}

data class Whnf(
    val expr: Expression,
    val levelSubst: Map<Int, Level> = emptyMap(),
)

context(env: Environment)
fun Expression.inferType(levelSubst: Map<Int, Level> = emptyMap(), localCtx: List<Expression> = emptyList()): Whnf {
    return when (this) {
        is Expression.App -> {
            val fnTy0 = this.fnExpr.inferType(levelSubst, localCtx)
            val fnTyWhnf = fnTy0.expr.reduce(fnTy0.levelSubst)
            val fnTy = fnTyWhnf.expr.instantiateLevelParams(fnTyWhnf.levelSubst)
            check(fnTy is Expression.ForallE) {
                "Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}"
            }
            val expectedArgTy = fnTy.typeExpr
            // TODO: this breaks in init-prelude
//            check(expectedArgTy.isDefEq(argTy, emptyMap(), argTy0.levelSubst, localCtx, localCtx)) {
//                "Application argument type mismatch in ${this.toStringDetailed()}: expected ${expectedArgTy.toStringDetailed()}, got ${argTy.toStringDetailed()}"
//            }
            val instantiatedBodyTy = fnTy.bodyExpr.applySubst(listOf(this.argExpr))
            Whnf(instantiatedBodyTy, levelSubst)
        }

        is Expression.Bvar -> {
            if (this.bvar < localCtx.size) {
                // live binder: its stored type was recorded outside this binder,
                // so lift it back under the current live-binder depth.
                Whnf(localCtx[this.bvar].lift(this.bvar + 1), levelSubst)
            } else {
                error("Unbound bvar ${this.bvar} in ${this.toStringDetailed()}")
            }
        }

        is Expression.Const -> {
            val ty = env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
            Whnf(ty, this.composeLevelSubst(levelSubst))
        }

        is Expression.ForallE -> {
            val left = this.typeExpr.inferSort(levelSubst, localCtx)
//            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")

            val right = this.bodyExpr.inferSort(levelSubst, listOf(this.typeExpr) + localCtx)

            val newLevel = env.addCustomLevel {
                Level.Imax(listOf(left.il, right.il), it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            Whnf(newExpr, levelSubst)
        }

        is Expression.Lam -> {
            val _ = this.typeExpr.inferSort(levelSubst, localCtx)
//            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")
            val bodyTyWhnf = this.bodyExpr.inferType(levelSubst, listOf(this.typeExpr) + localCtx)
            val reifiedBodyTy = bodyTyWhnf.expr.instantiateLevelParams(bodyTyWhnf.levelSubst)

            val newExpr = env.addCustomExpr {
                this.copyAsForAllE().copy(body = reifiedBodyTy.ie, ie = it)
            }
            Whnf(newExpr, levelSubst)
        }

        is Expression.Sort -> {
            val normalizedLevel = this.level.instantiateLevelParams(levelSubst)
            val newLevel = env.addCustomLevel {
                Level.Succ(normalizedLevel.il, it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            Whnf(newExpr, levelSubst)
        }

        is Expression.LetE -> {
            // We just need to check that the type is a sort (do we?), we don't need the exact level (potential optimization?)
            val _ = this.typeExpr.inferSort(levelSubst, localCtx)

            val valueTyWhnf = this.valueExpr.inferType(levelSubst, localCtx)
            check(this.typeExpr.isDefEq(valueTyWhnf.expr, levelSubst, valueTyWhnf.levelSubst, localCtx, localCtx)) {
                "Let value type mismatch in ${this.toStringDetailed()}: expected ${this.typeExpr.toStringDetailed()}, got ${valueTyWhnf.expr.toStringDetailed()}"
            }

            // Typechecking lets through localCtx alone loses let-definitional equality for nested dependent lets.
            // Use zeta-style inference directly on the instantiated body.
            this.bodyExpr
                .applySubst(listOf(this.valueExpr))
                .inferType(levelSubst, localCtx)
        }

        is Expression.Mdata -> TODO()
        is Expression.NatVal -> {
            val natInfo = env.findRootInductive("Nat")
                ?: error("Nat literal ${this.natVal} used without Nat inductive in environment")
            val natTypeIndex = natInfo.first
            val natTypeExpr = env.addCustomExpr {
                Expression.Const(_name = natTypeIndex, us = emptyList(), ie = it)
            }
            Whnf(natTypeExpr, levelSubst)
        }

        is Expression.Proj -> this.inferProjectionType(levelSubst, localCtx)
        is Expression.StrVal -> {
            val stringInfo = env.findRootInductive("String")
                ?: error("String literal used without String inductive in environment")
            val stringTypeIndex = stringInfo.first
            val stringTypeExpr = env.addCustomExpr {
                Expression.Const(_name = stringTypeIndex, us = emptyList(), ie = it)
            }
            Whnf(stringTypeExpr, levelSubst)
        }
    }
}

//context(env: Environment)
//fun Whnf.reduce(): Whnf = expr.reduce(levelSubst)

context(env: Environment)
fun Expression.reduce(levelSubst: Map<Int, Level> = emptyMap()): Whnf {
//    if (env.shouldLog) println("trying to reduce ${this.toStringDetailed()}")
    return when (this) {
        is Expression.App -> {
            val fnWhnf = this.fnExpr.reduce(levelSubst = levelSubst)
            when (val f = fnWhnf.expr) {
                is Expression.Lam -> {
                    // beta; instantiate levels in the lambda body first so constant-level
                    // substitutions do not leak into the substituted argument expression.
                    val instantiatedBody = f.bodyExpr.instantiateLevelParams(fnWhnf.levelSubst)
                    instantiatedBody.applySubst(listOf(this.argExpr)).reduce(levelSubst)
                }

                else -> {
                    val appExpr: Expression.App = if (f == this.fnExpr) {
                        this
                    } else {
                        env.addCustomExpr { this.copy(fn = f.ie, ie = it) } as Expression.App
                    }
                    appExpr.tryReduceRecursor(fnWhnf.levelSubst)
                        ?: appExpr.tryReduceQuot(fnWhnf.levelSubst)
                        ?: Whnf(appExpr, fnWhnf.levelSubst)
                }
            }
        }

        is Expression.Lam -> Whnf(this, levelSubst)
        is Expression.Bvar -> Whnf(this, levelSubst)
        is Expression.Const -> {
            val constLevelSubst = this.composeLevelSubst(levelSubst)
            when (val d = decl) {
                is Declaration.Def -> {
                    val instantiatedValue = d.valueExpr.instantiateLevelParams(constLevelSubst)
                    instantiatedValue.reduce(levelSubst)
                }

                else -> Whnf(this, constLevelSubst)
            }
        }

        is Expression.ForallE -> Whnf(this, levelSubst)
        is Expression.Sort -> Whnf(this, levelSubst)
        is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr)).reduce(levelSubst)
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> Whnf(this, levelSubst)

        is Expression.Proj -> {
            val structWhnf = this.structExpr.reduce(levelSubst)
            val [head, args] = structWhnf.expr.unfoldApp()
            val ctorConst = head as? Expression.Const
            val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
            if (
                ctorDecl != null &&
                ctorDecl.inductName == this.typeNameExpr &&
                this.projIndex in 0 until ctorDecl.numFields &&
                args.size == ctorDecl.numParams + ctorDecl.numFields
            ) {
                args[ctorDecl.numParams + this.projIndex].reduce(levelSubst)
            } else if (structWhnf.expr == this.structExpr) {
                Whnf(this, structWhnf.levelSubst)
            } else {
                val newExpr = env.addCustomExpr {
                    Expression.Proj(
                        typeName = this.typeNameIndex,
                        idx = this.projIndex,
                        struct = structWhnf.expr.ie,
                        ie = it,
                    )
                }
                Whnf(newExpr, structWhnf.levelSubst)
            }
        }

        is Expression.StrVal -> Whnf(this, levelSubst)
    }
}

context(env: Environment)
private fun Expression.Proj.inferProjectionType(levelSubst: Map<Int, Level>, localCtx: List<Expression>): Whnf {
    val structType0 = this.structExpr.inferType(levelSubst, localCtx)
    val structTypeWhnf = structType0.expr.reduce(structType0.levelSubst)
    val [structTypeHead, structTypeArgs] = structTypeWhnf.expr.unfoldApp()
    val structTypeConst = structTypeHead as? Expression.Const
        ?: error("Projection ${this.toStringDetailed()} expects structure type, got ${structTypeWhnf.expr.toStringDetailed()}")

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

    val projectionLevelSubst = structTypeConst.composeLevelSubst(structTypeWhnf.levelSubst)
    val paramArgs = structTypeArgs.take(constructorDecl.numParams)
    val structSort = structTypeWhnf.expr.inferSort(projectionLevelSubst, localCtx)
    val isPropStructure = structSort.isLessOrEqual(Level.Zero)
    val nonPropFieldIndices = mutableSetOf<Int>()

    var ctorType: Expression = constructorDecl.typeExpr
    repeat(constructorDecl.numParams + this.projIndex) { binderIndex ->
        val ctorForall = ctorType as? Expression.ForallE
            ?: error("Constructor ${constructorDecl.name} has too few binders while checking projection ${this.toStringDetailed()}")
        if (isPropStructure && binderIndex >= constructorDecl.numParams) {
            val priorFieldIndex = binderIndex - constructorDecl.numParams
            val priorFieldSort = ctorForall.typeExpr.inferSort(projectionLevelSubst, localCtx)
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
        val projectedSort = projectedType.inferSort(projectionLevelSubst, localCtx)
        check(projectedSort.isLessOrEqual(Level.Zero)) {
            "Projection ${this.toStringDetailed()} from proposition ${this.typeNameExpr} is not allowed because target field #${this.projIndex} is non-proposition ${projectedType.toStringDetailed()}"
        }
        check(!projectedType.containsProjectionOf(this.typeNameExpr, nonPropFieldIndices)) {
            "Projection ${this.toStringDetailed()} from proposition ${this.typeNameExpr} is not allowed because target field #${this.projIndex} depends on prior non-proposition data"
        }
    }

    return Whnf(projectedType, projectionLevelSubst)
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
private fun Expression.App.tryReduceRecursor(levelSubst: Map<Int, Level>): Whnf? {
    val unfolded = this.unfoldApp()
    val headExpr = unfolded.first
    val args = unfolded.second
    val recConst = headExpr as? Expression.Const ?: return null
    val recursorDecl = recConst.decl as? Inductive.RecursorVal ?: return null

    val majorArgIndex =
        recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors + recursorDecl.numIndices
    if (args.size <= majorArgIndex) return null

    val recursorArgsPrefixSize = recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors
    val prefixArgs = args.take(recursorArgsPrefixSize)

    fun applyRule(
        rule: Inductive.RecursorVal.RecursorRule,
        fieldArgs: List<Expression>,
        resultLevelSubst: Map<Int, Level>,
    ): Whnf {
        var reducedExpr: Expression = rule.rhsExpr
        (prefixArgs + fieldArgs).forEach { substArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, substArg.ie, it) }
        }
        args.drop(majorArgIndex + 1).forEach { extraArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, extraArg.ie, it) }
        }
        return reducedExpr.reduce(resultLevelSubst)
    }

    val majorWhnf = args[majorArgIndex].reduce(levelSubst)
    val [majorHead, majorArgs] = majorWhnf.expr.unfoldApp()

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
        return applyRule(matchingRule, fieldArgs, majorWhnf.levelSubst)
    }

    val majorNatLit = majorWhnf.expr as? Expression.NatVal
    if (majorNatLit != null) {
        if (majorNatLit.natVal !in 0L..MAX_NAT_LITERAL_RECURSOR_REDUCTION) return null
        val natRulesByFields: List<Pair<Int, Inductive.RecursorVal.RecursorRule>> =
            recursorDecl.rules.mapNotNull { rule ->
                val ctorDecl = env.declarations.values.filterIsInstance<Inductive.ConstructorVal>()
                    .singleOrNull { it.name == rule.ctorName } ?: return@mapNotNull null
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
                return if (majorNatLit.natVal == 0L) {
                    applyRule(zeroRule, emptyList(), majorWhnf.levelSubst)
                } else if (majorNatLit.natVal > 0L) {
                    val predNat = env.addCustomExpr { Expression.NatVal(majorNatLit.natVal - 1, it) }
                    applyRule(succRule, listOf(predNat), majorWhnf.levelSubst)
                } else {
                    null
                }
            }
        }
    }

    // K-like reduction: for recursors marked `k`, allow reducing neutral major premises
    // when their type forces the same constructor case with no constructor fields.
    if (!recursorDecl.k) return null
    val kRule = recursorDecl.rules.singleOrNull() ?: return null
    if (kRule.nfields != 0) return null
    val kCtorDecl = env.declarations.values.filterIsInstance<Inductive.ConstructorVal>().singleOrNull {
        it.name == kRule.ctorName
    } ?: return null
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
        if (!expectedIndexArgs[index].isDefEq(indexArgs[index], levelSubst, levelSubst)) {
            return null
        }
    }

    return applyRule(kRule, emptyList(), majorWhnf.levelSubst)
}

context(env: Environment)
private fun Expression.App.tryReduceQuot(levelSubst: Map<Int, Level>): Whnf? {
    val [headExpr, args] = this.unfoldApp()
    val quotConst = headExpr as? Expression.Const ?: return null
    val quotDecl = quotConst.decl as? Declaration.Quot ?: return null
    if (quotDecl.kind != Declaration.Quot.Kind.Lift && quotDecl.kind != Declaration.Quot.Kind.Ind) return null

    val arity = quotDecl.typeExpr.forallBinderCount()
    if (args.size < arity) return null

    val majorArg = args[arity - 1]
    val majorWhnf = majorArg.reduce(levelSubst)
    val [majorHead, majorArgs] = majorWhnf.expr.unfoldApp()
    val majorCtorConst = majorHead as? Expression.Const ?: return null
    val majorCtorDecl = majorCtorConst.decl as? Declaration.Quot ?: return null
    if (majorCtorDecl.kind != Declaration.Quot.Kind.Ctor) return null

    val ctorArity = majorCtorDecl.typeExpr.forallBinderCount()
    if (majorArgs.size < ctorArity || ctorArity == 0) return null
    val ctorValueArg = majorArgs[ctorArity - 1]

    val fnArg = when (quotDecl.kind) {
        Declaration.Quot.Kind.Lift -> {
            if (arity < 3) return null
            args[arity - 3]
        }

        Declaration.Quot.Kind.Ind -> {
            if (arity < 2) return null
            args[arity - 2]
        }
    }

    var reducedExpr: Expression = env.addCustomExpr {
        Expression.App(fn = fnArg.ie, arg = ctorValueArg.ie, ie = it)
    }
    args.drop(arity).forEach { extraArg: Expression ->
        reducedExpr = env.addCustomExpr { Expression.App(fn = reducedExpr.ie, arg = extraArg.ie, ie = it) }
    }
    return reducedExpr.reduce(majorWhnf.levelSubst)
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
    levelSubstLeft: Map<Int, Level>,
    levelSubstRight: Map<Int, Level>,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val leftType0 = this.inferType(levelSubstLeft, localCtxLeft)
    val rightType0 = other.inferType(levelSubstRight, localCtxRight)
    val leftTypeWhnf = leftType0.expr.reduce(leftType0.levelSubst)
    val rightTypeWhnf = rightType0.expr.reduce(rightType0.levelSubst)

    val [leftTypeHead, leftTypeArgs] = leftTypeWhnf.expr.unfoldApp()
    val [rightTypeHead, rightTypeArgs] = rightTypeWhnf.expr.unfoldApp()
    val leftTypeConst = leftTypeHead as? Expression.Const ?: return false
    val rightTypeConst = rightTypeHead as? Expression.Const ?: return false
    if (leftTypeConst.name != rightTypeConst.name) return false
    if (leftTypeArgs.size != rightTypeArgs.size) return false
    if (!leftTypeArgs.indices.all { i ->
            leftTypeArgs[i].isDefEq(
                rightTypeArgs[i],
                leftTypeWhnf.levelSubst,
                rightTypeWhnf.levelSubst,
                localCtxLeft,
                localCtxRight,
            )
        }) {
        return false
    }

    val typeNameIndex =
        env.names.entries.firstOrNull { entry -> entry.value == leftTypeConst.name }?.key ?: return false
    val structureDecl = env.declarations[typeNameIndex] as? Inductive.InductiveVal ?: return false
    if (structureDecl.isRec || structureDecl.ctors.size != 1 || structureDecl.numIndices != 0) return false
    val constructorDecl = env.declarations[structureDecl.ctors.single()] as? Inductive.ConstructorVal ?: return false
    if (constructorDecl.numParams != structureDecl.numParams) return false

    if (constructorDecl.numFields == 0) return true
    repeat(constructorDecl.numFields) { fieldIndex ->
        val lhsProj = env.addCustomExpr {
            Expression.Proj(typeName = typeNameIndex, idx = fieldIndex, struct = this@tryStructureEtaDefEq.ie, ie = it)
        }
        val rhsProj = env.addCustomExpr {
            Expression.Proj(typeName = typeNameIndex, idx = fieldIndex, struct = other.ie, ie = it)
        }
        if (!lhsProj.isDefEq(rhsProj, levelSubstLeft, levelSubstRight, localCtxLeft, localCtxRight)) {
            return false
        }
    }
    return true
}

context(env: Environment)
fun Expression.inferSort(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
): Level {
    val tyWhnf = this.inferType(levelSubst, localCtx)
    val whnfTy = tyWhnf.expr.reduce(tyWhnf.levelSubst)
    val sort = whnfTy.expr as? Expression.Sort
        ?: error("Expected Sort type for ${this.toStringDetailed()}, got ${whnfTy.expr.toStringDetailed()}")
    return sort.level.instantiateLevelParams(whnfTy.levelSubst)
}

context(env: Environment)
private fun Expression.tryEtaReduce(): Expression? {
    val lam = this as? Expression.Lam ?: return null
    val bodyApp = lam.bodyExpr as? Expression.App ?: return null
    val bodyArg = bodyApp.argExpr as? Expression.Bvar ?: return null
    if (bodyArg.bvar != 0) return null
    val fnExpr = bodyApp.fnExpr
    if (fnExpr.containsLooseBvarZero()) return null
    return fnExpr.dropOuterBinder()
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
private fun Expression.lift(amount: Int): Expression {
    if (amount == 0) return this

    return this.rewriteBinders { bvarExpr, depth ->
        if (bvarExpr.bvar >= depth) {
            env.addCustomExpr {
                bvarExpr.copy(bvar = bvarExpr.bvar + amount, ie = it)
            }
        } else {
            bvarExpr
        }
    }
}

context(env: Environment)
private fun Expression.instantiateLevelParams(subst: Map<Int, Level>): Expression {
    if (subst.isEmpty()) return this
    return when (this) {
        is Expression.Bvar -> this
        is Expression.NatVal -> this
        is Expression.StrVal -> this

        is Expression.Sort -> {
            val newLevel = this.level.instantiateLevelParams(subst)
            if (newLevel.sameShape(this.level)) this else env.addCustomExpr { this.copy(sort = newLevel.il, ie = it) }
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

    return this.rewriteBinders { bvarExpr, currentDepth ->
        when {
            bvarExpr.bvar < currentDepth -> bvarExpr
            bvarExpr.bvar - currentDepth < subst.size ->
                subst[bvarExpr.bvar - currentDepth].lift(currentDepth)

            else -> {
                env.addCustomExpr {
                    bvarExpr.copy(bvar = bvarExpr.bvar - subst.size, ie = it)
                }
            }
        }
    }
}

context(env: Environment)
private fun Expression.rewriteBinders(depth: Int = 0, rewriteBvar: (Expression.Bvar, Int) -> Expression): Expression {
    return when (this) {
        is Expression.Bvar -> rewriteBvar(this, depth)

        is Expression.App -> {
            val newFn = this.fnExpr.rewriteBinders(depth, rewriteBvar)
            val newArg = this.argExpr.rewriteBinders(depth, rewriteBvar)
            env.addCustomExpr {
                this.copy(fn = newFn.ie, arg = newArg.ie, ie = it)
            }
        }

        is Expression.ForallE -> {
            val newType = this.typeExpr.rewriteBinders(depth, rewriteBvar)
            val newBody = this.bodyExpr.rewriteBinders(depth + 1, rewriteBvar)
            env.addCustomExpr {
                this.copy(type = newType.ie, body = newBody.ie, ie = it)
            }
        }

        is Expression.Lam -> {
            val newType = this.typeExpr.rewriteBinders(depth, rewriteBvar)
            val newBody = this.bodyExpr.rewriteBinders(depth + 1, rewriteBvar)
            env.addCustomExpr {
                this.copy(type = newType.ie, body = newBody.ie, ie = it)
            }
        }

        is Expression.LetE -> {
            val newType = this.typeExpr.rewriteBinders(depth, rewriteBvar)
            val newValue = this.valueExpr.rewriteBinders(depth, rewriteBvar)
            val newBody = this.bodyExpr.rewriteBinders(depth + 1, rewriteBvar)
            env.addCustomExpr {
                this.copy(type = newType.ie, value = newValue.ie, body = newBody.ie, ie = it)
            }
        }

        is Expression.Mdata -> {
            val newExpr = this.expr.rewriteBinders(depth, rewriteBvar)
            env.addCustomExpr {
                this.copy(_expr = newExpr.ie, ie = it)
            }
        }

        is Expression.Proj -> {
            val newStruct = this.structExpr.rewriteBinders(depth, rewriteBvar)
            env.addCustomExpr {
                this.copy(struct = newStruct.ie, ie = it)
            }
        }

        else -> this
    }
}

context(env: Environment)
fun Level.instantiateLevelParams(subst: Map<Int, Level>): Level {
    return when (this) {
        Level.Zero -> this
        is Level.Param -> subst[this.il] ?: this

        is Level.Succ -> {
            val newLevel = this.level.instantiateLevelParams(subst)
            if (newLevel.sameShape(this.level)) {
                this
            } else {
                env.addCustomLevel { Level.Succ(newLevel.il, it) }
            }
        }

        is Level.Max -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft.sameShape(this.left) && newRight.sameShape(this.right)) {
                this
            } else {
                env.addCustomLevel { Level.Max(listOf(newLeft.il, newRight.il), it) }
            }
        }

        is Level.Imax -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft.sameShape(this.left) && newRight.sameShape(this.right)) {
                this
            } else {
                env.addCustomLevel { Level.Imax(listOf(newLeft.il, newRight.il), it) }
            }
        }
    }
}

context(env: Environment)
private fun Level.sameShape(other: Level): Boolean {
    return when (this) {
        is Level.Zero if other is Level.Zero -> true
        is Level.Param if other is Level.Param -> this.name == other.name
        is Level.Succ if other is Level.Succ -> this.level.sameShape(other.level)
        is Level.Max if other is Level.Max ->
            this.left.sameShape(other.left) && this.right.sameShape(other.right)

        is Level.Imax if other is Level.Imax ->
            this.left.sameShape(other.left) && this.right.sameShape(other.right)

        else -> false
    }
}

context(env: Environment)
private fun Environment.findRootInductive(shortName: String): Pair<Int, Inductive.InductiveVal>? {
    return this.declarations.entries.firstNotNullOfOrNull { entry ->
        val nameIndex = entry.key
        val inductiveDecl = entry.value as? Inductive.InductiveVal ?: return@firstNotNullOfOrNull null
        val name = this.names[nameIndex] as? Name.Str ?: return@firstNotNullOfOrNull null
        if (name.pre == 0 && name.str == shortName) {
            nameIndex to inductiveDecl
        } else {
            null
        }
    }
}

context(env: Environment)
private fun mergeLevelSubst(outer: Map<Int, Level>, inner: Map<Int, Level>): Map<Int, Level> {
    if (outer.isEmpty()) return inner
    if (inner.isEmpty()) return outer
    val normalizedInner = inner.mapValues { (key, value) ->
        val outerForKey = if (key in outer && outer.getValue(key).containsParamId(key)) {
            outer - key
        } else {
            outer
        }
        value.instantiateLevelParams(outerForKey)
    }
    return outer + normalizedInner
}

context(env: Environment)
private fun Level.containsParamId(paramId: Int): Boolean {
    return when (this) {
        Level.Zero -> false
        is Level.Param -> this.il == paramId
        is Level.Succ -> this.level.containsParamId(paramId)
        is Level.Max -> this.left.containsParamId(paramId) || this.right.containsParamId(paramId)
        is Level.Imax -> this.left.containsParamId(paramId) || this.right.containsParamId(paramId)
    }
}

context(env: Environment)
private fun Level.instantiateLevelParamsForConstEq(
    subst: Map<Int, Level>,
    depth: Int = 0,
): Level {
    return when (this) {
        Level.Zero -> this
        is Level.Param -> {
            val replacement = subst[this.il] ?: return this
            if (replacement.containsParamId(this.il)) {
                if (depth == 0) {
                    replacement.instantiateLevelParamsForConstEq(subst - this.il, depth)
                } else {
                    this
                }
            } else {
                replacement.instantiateLevelParamsForConstEq(subst, depth)
            }
        }

        is Level.Succ -> {
            val newLevel = this.level.instantiateLevelParamsForConstEq(subst, depth + 1)
            if (newLevel.sameShape(this.level)) {
                this
            } else {
                env.addCustomLevel { Level.Succ(newLevel.il, it) }
            }
        }

        is Level.Max -> {
            val newLeft = this.left.instantiateLevelParamsForConstEq(subst, depth + 1)
            val newRight = this.right.instantiateLevelParamsForConstEq(subst, depth + 1)
            if (newLeft.sameShape(this.left) && newRight.sameShape(this.right)) {
                this
            } else {
                env.addCustomLevel { Level.Max(listOf(newLeft.il, newRight.il), it) }
            }
        }

        is Level.Imax -> {
            val newLeft = this.left.instantiateLevelParamsForConstEq(subst, depth + 1)
            val newRight = this.right.instantiateLevelParamsForConstEq(subst, depth + 1)
            if (newLeft.sameShape(this.left) && newRight.sameShape(this.right)) {
                this
            } else {
                env.addCustomLevel { Level.Imax(listOf(newLeft.il, newRight.il), it) }
            }
        }
    }
}

context(env: Environment)
private fun Level.hasNestedSelfReferentialParam(
    subst: Map<Int, Level>,
    depth: Int = 0,
): Boolean {
    return when (this) {
        Level.Zero -> false
        is Level.Param -> depth > 0 && (subst[this.il]?.containsParamId(this.il) == true)
        is Level.Succ -> this.level.hasNestedSelfReferentialParam(subst, depth + 1)
        is Level.Max ->
            this.left.hasNestedSelfReferentialParam(subst, depth + 1) ||
                    this.right.hasNestedSelfReferentialParam(subst, depth + 1)

        is Level.Imax ->
            this.left.hasNestedSelfReferentialParam(subst, depth + 1) ||
                    this.right.hasNestedSelfReferentialParam(subst, depth + 1)
    }
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
    if (inner.isEmpty()) return outer
    if (outer.isEmpty()) return inner
    return mergeLevelSubst(outer, inner)
}