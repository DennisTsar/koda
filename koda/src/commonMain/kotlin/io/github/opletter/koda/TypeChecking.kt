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

context(env: Environment)
fun Expression.isDefEq(
    other: Expression,
    levelSubstLeft: Map<Int, Level> = emptyMap(),
    levelSubstRight: Map<Int, Level> = emptyMap(),
    localCtxLeft: List<Expression> = emptyList(),
    localCtxRight: List<Expression> = emptyList(),
): Boolean {
    val leftExpr = this.instantiateLevelParams(levelSubstLeft)
    val rightExpr = other.instantiateLevelParams(levelSubstRight)
    if (leftExpr == rightExpr) return true
    if (leftExpr.sameShape(rightExpr)) return true
    if (env.shouldLog) {
        println("comparing:\n$leftExpr\n$rightExpr")
    }
    val lhsWhnf = leftExpr.reduce()
    val rhsWhnf = rightExpr.reduce()
    return lhsWhnf.reifyWhnf().isDefEqWhnf(
        rhsWhnf.reifyWhnf(),
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
                    localCtxLeft = localCtxLeft,
                    localCtxRight = localCtxRight,
                )
            } else {
                val fnDefEq = this.fnExpr.isDefEq(
                    other.fnExpr,
                    localCtxLeft = localCtxLeft,
                    localCtxRight = localCtxRight,
                )
                if (!fnDefEq) {
                    return this.tryProofIrrelevanceDefEq(other, localCtxLeft, localCtxRight)
                }
                val argDefEq = this.argExpr.isDefEq(
                    other.argExpr,
                    localCtxLeft = localCtxLeft,
                    localCtxRight = localCtxRight,
                )
                if (!argDefEq) {
                    return this.tryProofIrrelevanceDefEq(other, localCtxLeft, localCtxRight)
                }
                true
            }
        }

        is Expression.App if other is Expression.NatVal ->
            this.tryUnfoldNatSuccChain()
                ?.let { chain ->
                    other.tryCompareWithNatSuccChain(
                        chain,
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
                    localCtxLeft = localCtxLeft,
                    localCtxRight = localCtxRight,
                )
                if (!typesDefEq) {
                    false
                } else {
                    val thisSort = thisType.inferSort(localCtx = localCtxLeft)
                    val otherSort = otherType.inferSort(localCtx = localCtxRight)
                    (thisSort.isLessOrEqual(Level.Zero) && otherSort.isLessOrEqual(Level.Zero))
                            || this.tryStructureEtaDefEq(
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
                    this.levels.zip(other.levels).all { [l1, l2] ->
                        l1.sameShape(l2) || l1.isEqual(l2)
                    }

        is Expression.ForallE if other is Expression.ForallE -> {
            this.typeExpr.isDefEq(
                other.typeExpr,
                localCtxLeft = localCtxLeft,
                localCtxRight = localCtxRight,
            ) &&
                    this.bodyExpr.isDefEq(
                        other.bodyExpr,
                        localCtxLeft = listOf(this.typeExpr) + localCtxLeft,
                        localCtxRight = listOf(other.typeExpr) + localCtxRight,
                    )
        }

        is Expression.Lam if other is Expression.Lam -> {
            this.typeExpr.isDefEq(
                other.typeExpr,
                localCtxLeft = localCtxLeft,
                localCtxRight = localCtxRight,
            ) &&
                    this.bodyExpr.isDefEq(
                        other.bodyExpr,
                        localCtxLeft = listOf(this.typeExpr) + localCtxLeft,
                        localCtxRight = listOf(other.typeExpr) + localCtxRight,
                    )
        }

        is Expression.Lam ->
            this.tryEtaReduce()
                ?.isDefEq(other, localCtxLeft = localCtxLeft, localCtxRight = localCtxRight)
                ?: false

        is Expression.LetE if other is Expression.LetE -> TODO()
        is Expression.Mdata if other is Expression.Mdata -> TODO()
        is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
        is Expression.NatVal if other is Expression.App ->
            other.tryUnfoldNatSuccChain()
                ?.let { chain ->
                    this.tryCompareWithNatSuccChain(
                        chain,
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
                        localCtxLeft = localCtxLeft,
                        localCtxRight = localCtxRight,
                    )

        is Expression.Sort if other is Expression.Sort -> this.level.isEqual(other.level)

        is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
        else -> {
            if (this.tryProofIrrelevanceDefEq(other, localCtxLeft, localCtxRight)) {
                return true
            }
            if (other is Expression.Lam) {
                other.tryEtaReduce()?.let {
                    return this.isDefEq(it, localCtxLeft = localCtxLeft, localCtxRight = localCtxRight)
                }
            }
            if (this.tryStructureEtaDefEq(other, localCtxLeft, localCtxRight)) {
                return true
            }
            val reducedThis = this.reduce().reifyWhnf()
            val reducedOther = other.reduce().reifyWhnf()
            if (reducedThis == this && reducedOther == other) {
                false
            } else {
                reducedThis.isDefEq(
                    reducedOther,
                    localCtxLeft = localCtxLeft,
                    localCtxRight = localCtxRight,
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
            baseExpr.isDefEq(
                remainingExpr,
                localCtxLeft = chainLocalCtx,
                localCtxRight = natLocalCtx,
            )
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
private fun Whnf.reifyWhnf(): Expression {
    return this.expr.instantiateLevelParams(this.levelSubst)
}

context(env: Environment)
fun Expression.inferType(levelSubst: Map<Int, Level> = emptyMap(), localCtx: List<Expression> = emptyList()): Whnf {
    return when (this) {
        is Expression.App -> {
            val fnTy0 = this.fnExpr.inferType(levelSubst, localCtx)
            val fnTyWhnf = fnTy0.expr.reduce(fnTy0.levelSubst)
            val fnTy = fnTyWhnf.reifyWhnf()
            check(fnTy is Expression.ForallE) {
                "Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}"
            }
            val expectedArgTy = fnTy.typeExpr
            // TODO: this breaks in init-prelude
//            check(expectedArgTy.isDefEq(argTy, emptyMap(), argTy0.levelSubst, localCtx, localCtx)) {
//                "Application argument type mismatch in ${this.toStringDetailed()}: expected ${expectedArgTy.toStringDetailed()}, got ${argTy.toStringDetailed()}"
//            }
            val instantiatedBodyTy = fnTy.bodyExpr.applySubst(listOf(this.argExpr))
            Whnf(instantiatedBodyTy.instantiateLevelParams(levelSubst))
        }

        is Expression.Bvar -> {
            if (this.bvar < localCtx.size) {
                // live binder: its stored type was recorded outside this binder,
                // so lift it back under the current live-binder depth.
                Whnf(localCtx[this.bvar].lift(this.bvar + 1).instantiateLevelParams(levelSubst))
            } else {
                error("Unbound bvar ${this.bvar} in ${this.toStringDetailed()}")
            }
        }

        is Expression.Const -> {
            val ty = env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
            Whnf(ty.instantiateLevelParams(this.composeLevelSubst(levelSubst)))
        }

        is Expression.ForallE -> {
            val left = this.typeExpr.inferSort(levelSubst, localCtx)
//            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")

            val right = this.bodyExpr.inferSort(levelSubst, listOf(this.typeExpr) + localCtx)

            val newLevel = env.addCustomLevel {
                Level.Imax(listOf(left.il, right.il), it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            Whnf(newExpr)
        }

        is Expression.Lam -> {
            val _ = this.typeExpr.inferSort(levelSubst, localCtx)
//            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")
            val bodyTyWhnf = this.bodyExpr.inferType(levelSubst, listOf(this.typeExpr) + localCtx)
            val reifiedBodyTy = bodyTyWhnf.reifyWhnf()

            val newExpr = env.addCustomExpr {
                this.copyAsForAllE().copy(body = reifiedBodyTy.ie, ie = it)
            }
            Whnf(newExpr)
        }

        is Expression.Sort -> {
            val normalizedLevel = this.level.instantiateLevelParams(levelSubst)
            val newLevel = env.addCustomLevel {
                Level.Succ(normalizedLevel.il, it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            Whnf(newExpr)
        }

        is Expression.LetE -> {
            // We just need to check that the type is a sort (do we?), we don't need the exact level (potential optimization?)
            val _ = this.typeExpr.inferSort(levelSubst, localCtx)

            val valueTyWhnf = this.valueExpr.inferType(levelSubst, localCtx)
            check(
                this.typeExpr.isDefEq(
                    valueTyWhnf.reifyWhnf(),
                    levelSubstLeft = levelSubst,
                    localCtxLeft = localCtx,
                    localCtxRight = localCtx
                )
            ) {
                "Let value type mismatch in ${this.toStringDetailed()}: expected ${this.typeExpr.toStringDetailed()}, got ${
                    valueTyWhnf.reifyWhnf().toStringDetailed()
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
            val natTypeExpr = env.addCustomExpr {
                Expression.Const(_name = natTypeIndex, us = emptyList(), ie = it)
            }
            Whnf(natTypeExpr)
        }

        is Expression.Proj -> this.inferProjectionType(levelSubst, localCtx)
        is Expression.StrVal -> {
            val stringInfo = env.findRootInductive("String")
                ?: error("String literal used without String inductive in environment")
            val stringTypeIndex = stringInfo.first
            val stringTypeExpr = env.addCustomExpr {
                Expression.Const(_name = stringTypeIndex, us = emptyList(), ie = it)
            }
            Whnf(stringTypeExpr)
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
            when (val f = fnWhnf.reifyWhnf()) {
                is Expression.Lam -> {
                    f.bodyExpr.applySubst(listOf(this.argExpr)).reduce(levelSubst)
                }

                else -> {
                    val appExpr: Expression.App = if (f == this.fnExpr) {
                        this.instantiateLevelParams(levelSubst) as Expression.App
                    } else {
                        env.addCustomExpr { this.copy(fn = f.ie, ie = it) } as Expression.App
                    }
                    appExpr.tryReduceRecursor(levelSubst)
                        ?: appExpr.tryReduceQuot(levelSubst)
                        ?: Whnf(appExpr.instantiateLevelParams(levelSubst))
                }
            }
        }

        is Expression.Lam -> Whnf(this.instantiateLevelParams(levelSubst))
        is Expression.Bvar -> Whnf(this)
        is Expression.Const -> {
            val constLevelSubst = this.composeLevelSubst(levelSubst)
            when (val d = decl) {
                is Declaration.Def -> {
                    val instantiatedValue = d.valueExpr.instantiateLevelParams(constLevelSubst)
                    instantiatedValue.reduce()
                }

                else -> Whnf(this.instantiateLevelParams(constLevelSubst))
            }
        }

        is Expression.ForallE -> Whnf(this.instantiateLevelParams(levelSubst))
        is Expression.Sort -> Whnf(this.instantiateLevelParams(levelSubst))
        is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr)).reduce(levelSubst)
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> Whnf(this)

        is Expression.Proj -> {
            val structExpr = this.structExpr.reduce(levelSubst).reifyWhnf()
            val [head, args] = structExpr.unfoldApp()
            val ctorConst = head as? Expression.Const
            val ctorDecl = ctorConst?.decl as? Inductive.ConstructorVal
            if (
                ctorDecl != null &&
                ctorDecl.inductName == this.typeNameExpr &&
                this.projIndex in 0 until ctorDecl.numFields &&
                args.size == ctorDecl.numParams + ctorDecl.numFields
            ) {
                args[ctorDecl.numParams + this.projIndex].reduce(levelSubst)
            } else if (structExpr == this.structExpr.instantiateLevelParams(levelSubst)) {
                Whnf(this.instantiateLevelParams(levelSubst))
            } else {
                val newExpr = env.addCustomExpr {
                    Expression.Proj(
                        typeName = this.typeNameIndex,
                        idx = this.projIndex,
                        struct = structExpr.ie,
                        ie = it,
                    )
                }
                Whnf(newExpr)
            }
        }

        is Expression.StrVal -> Whnf(this)
    }
}

context(env: Environment)
private fun Expression.Proj.inferProjectionType(levelSubst: Map<Int, Level>, localCtx: List<Expression>): Whnf {
    val structType0 = this.structExpr.inferType(levelSubst, localCtx)
    val structTypeExpr = structType0.expr.reduce(structType0.levelSubst).reifyWhnf()
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

    return Whnf(projectedType)
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
    val recursorLevelSubst = recConst.composeLevelSubst(levelSubst)

    val majorArgIndex =
        recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors + recursorDecl.numIndices
    if (args.size <= majorArgIndex) return null

    val recursorArgsPrefixSize = recursorDecl.numParams + recursorDecl.numMotives + recursorDecl.numMinors
    val prefixArgs = args.take(recursorArgsPrefixSize)

    fun applyRule(
        rule: Inductive.RecursorVal.RecursorRule,
        fieldArgs: List<Expression>,
        resultLevelSubst: Map<Int, Level> = emptyMap(),
    ): Whnf {
        var reducedExpr: Expression = rule.rhsExpr
        (prefixArgs + fieldArgs).forEach { substArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, substArg.ie, it) }
        }
        args.drop(majorArgIndex + 1).forEach { extraArg: Expression ->
            reducedExpr = env.addCustomExpr { Expression.App(reducedExpr.ie, extraArg.ie, it) }
        }
        val mergedSubst = mergeLevelSubst(recursorLevelSubst, resultLevelSubst)
        return reducedExpr.reduce(mergedSubst)
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
        if (!expectedIndexArgs[index].isDefEq(indexArgs[index], recursorLevelSubst, recursorLevelSubst)) {
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
    val quotLevelSubst = quotConst.composeLevelSubst(levelSubst)

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
    val mergedSubst = mergeLevelSubst(quotLevelSubst, majorWhnf.levelSubst)
    return reducedExpr.reduce(mergedSubst)
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
    val leftType0 = this.inferType(localCtx = localCtxLeft)
    val rightType0 = other.inferType(localCtx = localCtxRight)
    val leftTypeExpr = leftType0.expr.reduce(leftType0.levelSubst).reifyWhnf()
    val rightTypeExpr = rightType0.expr.reduce(rightType0.levelSubst).reifyWhnf()

    val [leftTypeHead, leftTypeArgs] = leftTypeExpr.unfoldApp()
    val [rightTypeHead, rightTypeArgs] = rightTypeExpr.unfoldApp()
    val leftTypeConst = leftTypeHead as? Expression.Const ?: return false
    val rightTypeConst = rightTypeHead as? Expression.Const ?: return false
    if (leftTypeConst.name != rightTypeConst.name) return false
    if (leftTypeArgs.size != rightTypeArgs.size) return false
    if (!leftTypeArgs.indices.all { i ->
            leftTypeArgs[i].isDefEq(
                rightTypeArgs[i],
                localCtxLeft = localCtxLeft,
                localCtxRight = localCtxRight,
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
        if (!lhsProj.isDefEq(rhsProj, localCtxLeft = localCtxLeft, localCtxRight = localCtxRight)) {
            return false
        }
    }
    return true
}

context(env: Environment)
private fun Expression.tryProofIrrelevanceDefEq(
    other: Expression,
    localCtxLeft: List<Expression>,
    localCtxRight: List<Expression>,
): Boolean {
    val thisTy0 = this.inferType(localCtx = localCtxLeft)
    val otherTy0 = other.inferType(localCtx = localCtxRight)
    val thisTy = thisTy0.expr.reduce(thisTy0.levelSubst).reifyWhnf()
    val otherTy = otherTy0.expr.reduce(otherTy0.levelSubst).reifyWhnf()
    val thisSort = thisTy.inferSort(localCtx = localCtxLeft)
    val otherSort = otherTy.inferSort(localCtx = localCtxRight)
    if (!thisSort.isLessOrEqual(Level.Zero) || !otherSort.isLessOrEqual(Level.Zero)) {
        return false
    }
    return thisTy.isDefEq(
        otherTy,
        localCtxLeft = localCtxLeft,
        localCtxRight = localCtxRight,
    )
}

context(env: Environment)
fun Expression.inferSort(
    levelSubst: Map<Int, Level> = emptyMap(),
    localCtx: List<Expression> = emptyList(),
): Level {
    val tyWhnf = this.inferType(levelSubst, localCtx)
    val whnfTyExpr = tyWhnf.expr.reduce(tyWhnf.levelSubst).reifyWhnf()
    val sort = whnfTyExpr as? Expression.Sort
        ?: error("Expected Sort type for ${this.toStringDetailed()}, got ${whnfTyExpr.toStringDetailed()}")
    return sort.level
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
fun Expression.instantiateLevelParams(subst: Map<Int, Level>): Expression {
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
    val normalizedInner = inner.mapValues { entry -> entry.value.instantiateLevelParams(outer) }
    return outer + normalizedInner
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
