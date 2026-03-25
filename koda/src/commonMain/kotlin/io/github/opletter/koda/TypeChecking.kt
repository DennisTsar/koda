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
    rawData.forEachIndexed { index, data ->
        //i: progress = 1000000 13.462160800s
        //i: progress = 1100000 24.175118s
        //..
        //i: progress = 1122250 24.465904400s
        //i: progress = 1122251 36.557328900s
        //...
        //i: progress = 1122611 36.558250900s
        //i: progress = 1122612 48.691833300s
        if (index != 0 && index % 10_000 == 0) {
            println("i: progress = $index ${env.clock.elapsedNow()}")
        }
//        if (index == 1384359) {
//            env.shouldLog = true
//        }
//        if (index > 1384359) {
//            return
//        }
//        if (index == 1122250 || index == 1122611) {
//            env.shouldLog = true
//        } else {
//            env.shouldLog = false
//        }
        //1011000//1120000//1122000
//        if (index == 1120000)
//            env.shouldLog2 = true
        if (env.shouldLog) {
            println("started: ${env.clock.elapsedNow()}")
            println("${(data as NamedDecl).name.toStringDetailed()} $data")
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

                env.declTypeByName[data.name] = data.typeExpr

                // (4): "the declaration's type has no free variables"
                // TODO
            }

            is Inductive -> {
                checkInductive(data)
            }

            is Meta -> {} // no-op
        }
        if (env.shouldLog) {
            println(
                "stats: defEqCalls=${env.defEqCalls} defEqCacheHits=${env.defEqCacheHits} " +
                        "defEqInProgressSkips=${env.defEqInProgressSkips} defEqCacheSize=${env.defEqCache.size}"
            )
        }
        env.clearCustom()
        if (env.shouldLog) {
            println("ended: ${env.clock.elapsedNow()}")
        }
//        println("apple: ${env.levels.size} // ${env.expressions.size} // ${env.declarations.size} // ${env.names.size}")
    }
}

context(env: Environment)
fun typeCheckDeclaration(value: Expression, expectedType: Expression): Boolean {
    if (env.shouldLog) println("found value: ${value/*.toStringDetailed()*/}")
    val inferredValueType = value.inferType() // MEM: 200 MB
    if (env.shouldLog) println("inferred type of value: ${inferredValueType/*.toStringDetailed()*/}")
    val actualType = inferredValueType
    // made it to: Def(_name=2098, _levelParams=[22, 6], type=12166, value=12236, hints=Abbrev, safety=Safe, all=[2098])
    // before Java heap space error, ran for 1 min 21 sec
    //    return Blah.isDefEq(Everything(env, expectedType, actualType, levelSubstRight = inferredValueType.levelSubst))
    // made it to: Def(_name=1944, _levelParams=[6], type=10830, value=10837, hints=Abbrev, safety=Safe, all=[1944])
    // before stack overflow, ran for 30 sec
    return expectedType.isDefEq(actualType) // MEM: 13 GB
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
        return false
    }

    val result = try {
        if (leftExpr == rightExpr) {
            true
        } else if (leftExpr.sameShape(rightExpr)) {
            true // MEM: 180 MB
        } else {
//    if (env.shouldLog) {
//        println("comparing:\n${leftExpr}\n${rightExpr}")
//    }
            if (
                leftExpr.isWhnfByShape() &&
                rightExpr.isWhnfByShape() &&
                leftExpr.isDefEqWhnf(rightExpr, localCtxLeft, localCtxRight)
            ) {
                true
            } else {
                val leftWhnfExpr = if (leftExpr.isWhnfByShape()) leftExpr else leftExpr.reduce() // MEM: 6.3 GB
                val rightWhnfExpr = if (rightExpr.isWhnfByShape()) rightExpr else rightExpr.reduce() // MEM: 6.3 GB
//    if (env.shouldLog) {
//        println("comparing (reduced):\n${leftWhnfExpr}\n${rightWhnfExpr}")
//    }
                if (leftWhnfExpr == rightWhnfExpr) {
                    true
                } else if (leftWhnfExpr.isDefEqWhnf(rightWhnfExpr, localCtxLeft, localCtxRight)) {
                    true // MEM: 13 GB
                } else {
                    val tempLog = env.shouldLog
                    env.shouldLog = false
                    leftWhnfExpr.tryProofIrrelevanceDefEq(rightWhnfExpr, localCtxLeft, localCtxRight)
                        .also { env.shouldLog = tempLog }
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
private fun Expression.isWhnfByShape(): Boolean = when (this) {
    is Expression.Bvar,
    is Expression.ForallE,
    is Expression.Lam,
    is Expression.NatVal,
    is Expression.Sort,
    is Expression.StrVal -> true

    is Expression.Const -> this.decl !is Declaration.Def

    is Expression.App,
    is Expression.LetE,
    is Expression.Mdata,
    is Expression.Proj -> false
}

context(env: Environment)
private fun Expression.sameShape(other: Expression): Boolean = when (this) {
    else if this.ie == other.ie -> true
    is Expression.Bvar if other is Expression.Bvar -> this.bvar == other.bvar
    is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
    is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
    is Expression.Sort if other is Expression.Sort -> this.level == other.level//this.level.sameShape(other.level)
    is Expression.Const if other is Expression.Const ->
        this.name == other.name &&
                this.levels.size == other.levels.size &&
                this.levels.zip(other.levels).all { it.first == it.second }

    is Expression.App if other is Expression.App ->
        this.fnExpr.sameShape(other.fnExpr) && this.argExpr.sameShape(other.argExpr) // MEM: 160 MB

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

context(env: Environment)
private fun Expression.isDefEqWhnf(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean = when (this) {
    is Expression.App if other is Expression.App -> {
        val lhsNat = this.tryUnfoldNatSuccChain()
        val rhsNat = other.tryUnfoldNatSuccChain()
        if (lhsNat != null && rhsNat != null && lhsNat.count == rhsNat.count) {
            lhsNat.base.isDefEq(rhsNat.base, localCtxLeft, localCtxRight)
        } else {
            this.fnExpr.isDefEq(other.fnExpr, localCtxLeft, localCtxRight) && // MEM: 12.7 GB
                    this.argExpr.isDefEq(other.argExpr, localCtxLeft, localCtxRight) // MEM: 12.8 GB
        }
    }

    is Expression.App if other is Expression.NatVal ->
        this.tryUnfoldNatSuccChain()
            ?.let { chain ->
                other.tryCompareWithNatSuccChain(chain, localCtxLeft, localCtxRight)
            } ?: false

    is Expression.Bvar if other is Expression.Bvar -> {
        if (this.bvar == other.bvar) {
            true
        } else if (this.bvar < localCtxLeft.size && other.bvar < localCtxRight.size) {
            val thisType = localCtxLeft[this.bvar].lift(this.bvar + 1)
            val otherType = localCtxRight[other.bvar].lift(other.bvar + 1)
            val typesDefEq = thisType.isDefEq(otherType, localCtxLeft, localCtxRight)
            if (!typesDefEq) {
                false
            } else {
                this.tryStructureEtaDefEq(
                    other,
                    localCtxLeft,
                    localCtxRight,
                )
            }
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
        this.typeExpr.isDefEq(other.typeExpr, localCtxLeft, localCtxRight) && // MEM: 3 GB
                this.bodyExpr.isDefEq(
                    // MEM: 12.9 GB
                    other.bodyExpr,
                    listOf(this.typeExpr) + localCtxLeft,
                    listOf(other.typeExpr) + localCtxRight,
                )
    }

    is Expression.Lam if other is Expression.Lam -> {
        this.typeExpr.isDefEq(other.typeExpr, localCtxLeft, localCtxRight) && // MEM: 5.2 GB
                this.bodyExpr.isDefEq(
                    // MEM: 12.2 GB
                    other.bodyExpr,
                    listOf(this.typeExpr) + localCtxLeft,
                    listOf(other.typeExpr) + localCtxRight,
                )
    }

    is Expression.Lam ->
        this.tryEtaReduce()
            ?.isDefEq(other, localCtxLeft, localCtxRight)
            ?: false

    is Expression.LetE if other is Expression.LetE -> TODO()
    is Expression.Mdata if other is Expression.Mdata -> TODO()
    is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
    is Expression.NatVal if other.isNatZeroCtorConst() -> this.natVal.isZero()
    is Expression.NatVal if other is Expression.App ->
        other.tryUnfoldNatSuccChain()
            ?.let { chain ->
                this.tryCompareWithNatSuccChain(chain, chainLocalCtx = localCtxRight, natLocalCtx = localCtxLeft)
            } ?: false

    is Expression.Const if this.isNatZeroCtorConst() && other is Expression.NatVal -> other.natVal.isZero()
    is Expression.Proj if other is Expression.Proj ->
        this.typeNameExpr == other.typeNameExpr &&
                this.projIndex == other.projIndex &&
                this.structExpr.isDefEq(other.structExpr, localCtxLeft, localCtxRight) // MEM: 10.5 GB

    is Expression.Sort if other is Expression.Sort -> this.level.isEqual(other.level)

    is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
    else -> {
        if (other is Expression.Lam) {
            other.tryEtaReduce()?.let {
                return this.isDefEq(it, localCtxLeft, localCtxRight)
            }
        }
        if (
            this.canBeStructureLikeValue() &&
            other.canBeStructureLikeValue() &&
            this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight)
        ) {
            return true
        }
        val reducedThis = this.reduce()
        val reducedOther = other.reduce()
        if (reducedThis == this && reducedOther == other) {
            false
        } else {
            reducedThis.isDefEq(reducedOther, localCtxLeft, localCtxRight)
        }
    }
}

private fun Expression.canBeStructureLikeValue(): Boolean = when (this) {
    is Expression.App,
    is Expression.Bvar,
    is Expression.Const,
    is Expression.LetE,
    is Expression.Mdata,
    is Expression.Proj -> true

    else -> false
}

private data class NatSuccChain(
    val count: Long,
    val base: Expression,
)

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
    chainLocalCtx: List<Expression>,
    natLocalCtx: List<Expression>,
): Boolean {
    if (this.natVal.compareTo(chain.count) < 0) return false
    val remaining = this.natVal.minus(chain.count)
    val baseExpr = chain.base
    return when {
        baseExpr is Expression.NatVal -> baseExpr.natVal == remaining
        baseExpr.isNatZeroCtorConst() -> remaining.isZero()
        else -> {
            val remainingExpr = env.addCustomExpr { Expression.NatVal(remaining, it) }
            baseExpr.isDefEq(remainingExpr, chainLocalCtx, natLocalCtx)
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

context(env: Environment)
fun Expression.inferType(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList()
): Expression {
    return when (this) {
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
            val fnTy = fnTy0.reduce()
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

            val valueTyWhnf = this.valueExpr.inferType(levelSubst, localCtx)
            val expectedTypeExpr = this.typeExpr.instantiateLevelParams(levelSubst)
            check(expectedTypeExpr.isDefEq(valueTyWhnf, localCtx, localCtx)) {
                "Let value type mismatch in ${this.toStringDetailed()}: expected ${expectedTypeExpr.toStringDetailed()}, got ${
                    valueTyWhnf.toStringDetailed()
                }"
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
}

context(env: Environment)
fun Expression.reduce(levelSubst: Map<Int, Level> = emptyMap()): Expression {
    if (levelSubst.isEmpty()) {
        env.reduceCacheNoLevelSubst[this.ie]?.let { return it }
    }
    if (env.shouldLog) println("trying to reduce ${this}")
    val result = when (this) {
        is Expression.App -> {
            if (!this.fnExpr.canReduceAtHead()) {
                this.tryReduceRecursor(levelSubst) // MEM: 3.6 GB
                    ?: this.tryReduceQuot(levelSubst)
                    ?: this.instantiateLevelParams(levelSubst)
            } else {
                when (val fnWhnf = this.fnExpr.reduce(levelSubst)) { // MEM: 10.1 GB
                    is Expression.Lam -> {
                        fnWhnf.bodyExpr.applySubst(listOf(this.argExpr)).reduce() // MEM: 12.2 GB
                    }

                    else -> {
                        val appExprPreInst: Expression.App = if (fnWhnf == this.fnExpr) {
                            this
                        } else {
                            env.addCustomExpr { this.copy(fn = fnWhnf.ie, ie = it) } as Expression.App
                        }
                        val reducedApp = appExprPreInst.tryReduceRecursor(levelSubst)
                            ?: appExprPreInst.tryReduceQuot(levelSubst)
                        if (reducedApp != null) {
                            reducedApp
                        } else {
                            val appExpr = appExprPreInst.instantiateLevelParams(levelSubst)
                            if (fnWhnf != this.fnExpr) appExpr.reduce() else appExpr // MEM: 200 MB
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
                    val constLevelSubst = this.composeLevelSubst(levelSubst) // MEM: 300 MB
                    val instantiatedValue = d.valueExpr.instantiateLevelParams(constLevelSubst)
                    instantiatedValue.reduce()
                }

                else -> this.instantiateLevelParams(levelSubst)
            }
        }

        is Expression.ForallE -> this.instantiateLevelParams(levelSubst)
        is Expression.Sort -> this.instantiateLevelParams(levelSubst)
        is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr)).reduce(levelSubst)
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> this

        is Expression.Proj -> {
            val structExpr = this.structExpr.reduce(levelSubst) // MEM: 2 GB
            val [head, args] = structExpr.unfoldApp()
            val ctorConst = head as? Expression.Const
            val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
            if (
                ctorDecl != null &&
                ctorDecl.inductName == this.typeNameExpr &&
                this.projIndex in 0 until ctorDecl.numFields &&
                args.size == ctorDecl.numParams + ctorDecl.numFields
            ) {
                args[ctorDecl.numParams + this.projIndex].reduce()
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
    if (levelSubst.isEmpty()) {
        env.reduceCacheNoLevelSubst[this.ie] = result
    }
    return result
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
private fun Expression.Proj.inferProjectionType(levelSubst: Map<Int, Level>, localCtx: List<Expression>): Expression {
    val structType0 = this.structExpr.inferType(levelSubst, localCtx)
    val structTypeExpr = structType0.reduce()
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
private fun Expression.App.tryReduceRecursor(levelSubst: Map<Int, Level>): Expression? {
    val unfolded = this.unfoldApp() // MEM: 100 MB
    val headExpr = unfolded.first
    val args = unfolded.second
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
        var reducedExpr: Expression = rule.rhsExpr
        (prefixArgs + fieldArgs).forEach { substArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, substArg.ie, it) }
        }
        args.drop(majorArgIndex + 1).forEach { extraArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, extraArg.ie, it) }
        }
        return reducedExpr.reduce(recursorLevelSubst) // MEM: 1 GB
    }

    val majorWhnf = args[majorArgIndex].reduce(levelSubst) // MEM: 2.5 GB
    val [majorHead, majorArgs] = majorWhnf.unfoldApp()

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
        return applyRule(matchingRule, fieldArgs) // MEM: 1 GB
    }

    val majorNatLit = majorWhnf as? Expression.NatVal
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

    // Structure-style constructor-parameter reduction on neutral major premises:
    // for non-rec, non-indexed single-constructor inductives, recursor applications can
    // be reduced by substituting projections of the major premise as constructor fields.
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

    // K-like reduction: for recursors marked `k`, allow reducing neutral major premises
    // when their type forces the same constructor case with no constructor fields.
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
        if (!expectedIndex.isDefEq(actualIndex)) {
            return null
        }
    }

    return applyRule(kRule, emptyList())
}

context(env: Environment)
private fun Expression.App.tryReduceQuot(levelSubst: Map<Int, Level>): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val quotConst = headExpr as? Expression.Const ?: return null
    val quotDecl = quotConst.decl as? Declaration.Quot ?: return null
    if (quotDecl.kind != Declaration.Quot.Kind.Lift && quotDecl.kind != Declaration.Quot.Kind.Ind) return null
    val arity = quotDecl.typeExpr.forallBinderCount()
    if (args.size < arity) return null

    val majorArg = args[arity - 1]
    val majorWhnf = majorArg.reduce(levelSubst) // MEM: 346 GB
    val [majorHead, majorArgs] = majorWhnf.unfoldApp()
    val majorCtorConst = majorHead as? Expression.Const ?: return null
    val majorCtorDecl = majorCtorConst.decl as? Declaration.Quot ?: return null
    if (majorCtorDecl.kind != Declaration.Quot.Kind.Ctor) return null

    val ctorArity = majorCtorDecl.typeExpr.forallBinderCount()
    if (majorArgs.size < ctorArity || ctorArity == 0) return null
    val ctorValueArg = majorArgs[ctorArity - 1]

    val fnArg = when (quotDecl.kind) {
        Declaration.Quot.Kind.Lift -> args.getOrNull(arity - 3) ?: return null
        Declaration.Quot.Kind.Ind -> args.getOrNull(arity - 2) ?: return null
    }

    var reducedExpr: Expression = env.addCustomExpr {
        Expression.App(fn = fnArg.ie, arg = ctorValueArg.ie, ie = it)
    }
    args.drop(arity).forEach { extraArg: Expression ->
        reducedExpr = env.addCustomExpr { Expression.App(fn = reducedExpr.ie, arg = extraArg.ie, ie = it) }
    }
    return reducedExpr.reduce()
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
    if (!env.structureEtaInProgress.add(guardKey)) {
        return false
    }
    try {
        if (!this.hasNoUnboundBvars(localCtxLeft.size) || !other.hasNoUnboundBvars(localCtxRight.size)) {
            return false
        }
        val leftType0 = this.inferType(localCtx = localCtxLeft)
        val rightType0 = other.inferType(localCtx = localCtxRight)
        val leftTypeExpr = leftType0.reduce()
        val rightTypeExpr = rightType0.reduce()

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
        if (structureDecl.isRec || structureDecl.ctors.size != 1 || structureDecl.numIndices != 0) return false
        val constructorDecl =
            env.declarations[structureDecl.ctors.single()] as? Inductive.ConstructorVal ?: return false
        if (constructorDecl.numParams != structureDecl.numParams) return false

        if (constructorDecl.numFields == 0) return true
        repeat(constructorDecl.numFields) { fieldIndex ->
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
            if (!lhsProj.isDefEq(rhsProj, localCtxLeft, localCtxRight)) {
                return false
            }
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
    val whnfTyExpr = tyWhnf.reduce()
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
    lam.tryEtaReduceHead()?.let { return it }

    val innerLam = lam.bodyExpr as? Expression.Lam ?: return null
    val reducedInner = innerLam.tryEtaReduce() ?: return null
    val rebuiltLam = env.addCustomExpr { lam.copy(body = reducedInner.ie, ie = it) } as? Expression.Lam
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
private fun Expression.hasNoUnboundBvars(localCtxSize: Int, depth: Int = 0): Boolean {
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
private fun Expression.lift(amount: Int): Expression {
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
    return when (this) {
        is Expression.Bvar -> rewriteBvar(this, depth)

        is Expression.App -> {
            val newFn = this.fnExpr.rewriteBinders(depth, rewriteBvar) // MEM: 9.7 GB
            val newArg = this.argExpr.rewriteBinders(depth, rewriteBvar) // MEM: 9.5 GB
            if (newFn === this.fnExpr && newArg === this.argExpr) {
                this
            } else {
                env.addCustomExpr { // MEM: 5.4 GB
                    this.copy(fn = newFn.ie, arg = newArg.ie, ie = it) // MEM: 1.3 GB
                }
            }
        }

        is Expression.ForallE -> {
            val newType = this.typeExpr.rewriteBinders(depth, rewriteBvar) // MEM: 1.3 GB
            val newBody = this.bodyExpr.rewriteBinders(depth + 1, rewriteBvar) // MEM: 2 GB
            if (newType === this.typeExpr && newBody === this.bodyExpr) {
                this
            } else {
                env.addCustomExpr {// MEM: 120 MB
                    this.copy(type = newType.ie, body = newBody.ie, ie = it)
                }
            }
        }

        is Expression.Lam -> {
            val newType = this.typeExpr.rewriteBinders(depth, rewriteBvar) // MEM: 5.9 GB
            val newBody = this.bodyExpr.rewriteBinders(depth + 1, rewriteBvar) // MEM: 9.6 GB
            if (newType === this.typeExpr && newBody === this.bodyExpr) {
                this
            } else {
                env.addCustomExpr { // MEM: 800 MB
                    this.copy(type = newType.ie, body = newBody.ie, ie = it) // MEM: 180 MB
                }
            }
        }

        is Expression.LetE -> {
            val newType = this.typeExpr.rewriteBinders(depth, rewriteBvar) // MEM: 110 MB
            val newValue = this.valueExpr.rewriteBinders(depth, rewriteBvar)
            val newBody = this.bodyExpr.rewriteBinders(depth + 1, rewriteBvar)
            if (newType === this.typeExpr && newValue === this.valueExpr && newBody === this.bodyExpr) {
                this
            } else {
                env.addCustomExpr {
                    this.copy(type = newType.ie, value = newValue.ie, body = newBody.ie, ie = it)
                }
            }
        }

        is Expression.Mdata -> {
            val newExpr = this.expr.rewriteBinders(depth, rewriteBvar)
            if (newExpr === this.expr) {
                this
            } else {
                env.addCustomExpr {
                    this.copy(_expr = newExpr.ie, ie = it)
                }
            }
        }

        is Expression.Proj -> {
            val newStruct = this.structExpr.rewriteBinders(depth, rewriteBvar) // MEM: 190 MB
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

private fun Environment.findRootInductive(shortName: String): Pair<Int, Inductive.InductiveVal>? {
    return this.rootInductiveByShortName[shortName]
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
    val normalizedInner = inner.mapValues { entry -> entry.value.instantiateLevelParams(outer) }
    return outer + normalizedInner
}