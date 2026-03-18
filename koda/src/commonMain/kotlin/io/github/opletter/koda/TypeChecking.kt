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
                println("found type: ${data.typeExpr.toStringDetailed()}")
                val declaredTypeSortLevel = data.typeExpr.inferSort()

                when (data) {
                    is Declaration.Axiom -> {} // no extra checks needed
                    is Declaration.Def -> {
                        check(typeCheckDeclaration(data.valueExpr, data.typeExpr)) {
                            "value not defeq to type for $data"
                        }
                    }

                    is Declaration.Opaque -> TODO()
                    is Declaration.Quot -> TODO()
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

            else -> {}
        }
    }
}

context(env: Environment)
fun typeCheckDeclaration(value: Expression, expectedType: Expression): Boolean {
    println("found value: ${value.toStringDetailed()}")
    val inferredValueType = value.inferType()
    println("inferred type of value: ${inferredValueType.expr.toStringDetailed()}")
    val actualType = inferredValueType.expr
    return expectedType.isDefEq(actualType, levelSubstRight = inferredValueType.levelSubst)
}

context(env: Environment)
fun Expression.isDefEq(
    other: Expression,
    levelSubstLeft: Map<Int, Level> = emptyMap(),
    levelSubstRight: Map<Int, Level> = emptyMap(),
): Boolean {
    val lhsWhnf = this.reduce(levelSubst = levelSubstLeft)
    val rhsWhnf = other.reduce(levelSubst = levelSubstRight)
    return lhsWhnf.expr.isDefEqWhnf(rhsWhnf.expr, lhsWhnf.levelSubst, rhsWhnf.levelSubst)
}

context(env: Environment)
private fun Expression.isDefEqWhnf(
    other: Expression,
    levelSubstLeft: Map<Int, Level>,
    levelSubstRight: Map<Int, Level>,
): Boolean {
    return when (this) {
        is Expression.App if other is Expression.App ->
            this.fnExpr.isDefEq(other.fnExpr, levelSubstLeft, levelSubstRight) &&
                    this.argExpr.isDefEq(other.argExpr, levelSubstLeft, levelSubstRight)

        is Expression.Bvar if other is Expression.Bvar -> this.bvar == other.bvar

        is Expression.Const if other is Expression.Const ->
            this.name == other.name &&
                    this.levels.size == other.levels.size &&
                    this.levels.zip(other.levels).all { [l1, l2] ->
                        l1.instantiateLevelParams(levelSubstLeft)
                            .isEqual(l2.instantiateLevelParams(levelSubstRight))
                    }

        is Expression.ForallE if other is Expression.ForallE -> {
            this.typeExpr.isDefEq(other.typeExpr, levelSubstLeft, levelSubstRight) &&
                    this.bodyExpr.isDefEq(other.bodyExpr, levelSubstLeft, levelSubstRight)
        }

        is Expression.Lam if other is Expression.Lam -> {
            this.typeExpr.isDefEq(other.typeExpr, levelSubstLeft, levelSubstRight) &&
                    this.bodyExpr.isDefEq(other.bodyExpr, levelSubstLeft, levelSubstRight)
        }

        is Expression.LetE if other is Expression.LetE -> TODO()
        is Expression.Mdata if other is Expression.Mdata -> TODO()
        is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
        is Expression.Proj if other is Expression.Proj -> TODO()
        is Expression.Sort if other is Expression.Sort ->
            this.level.instantiateLevelParams(levelSubstLeft)
                .isEqual(other.level.instantiateLevelParams(levelSubstRight))

        is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
        else -> TODO("DefEq not implemented for ${this::class.simpleName} and ${other::class.simpleName}")
    }
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
            val fnTy = fnTyWhnf.expr
            check(fnTy is Expression.ForallE) {
                "Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}"
            }
            val argTy0 = this.argExpr.inferType(levelSubst, localCtx)
            val argTy = argTy0.expr
            val expectedArgTy = fnTy.typeExpr
            check(expectedArgTy.isDefEq(argTy, fnTyWhnf.levelSubst, argTy0.levelSubst)) {
                "Application argument type mismatch in ${this.toStringDetailed()}: expected ${expectedArgTy.toStringDetailed()}, got ${argTy.toStringDetailed()}"
            }
            val instantiatedBodyTy = fnTy.bodyExpr.applySubst(listOf(this.argExpr))
            Whnf(instantiatedBodyTy, fnTyWhnf.levelSubst)
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
            Whnf(ty, composeLevelSubst(levelSubst, this.levelSubstMap()))
        }

        is Expression.ForallE -> {
            val left = this.typeExpr.inferSort(levelSubst, localCtx)
            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")

            val right = this.bodyExpr.inferSort(levelSubst, listOf(this.typeExpr) + localCtx)

            val newLevel = env.addCustomLevel {
                Level.Imax(listOf(left.il, right.il), it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel.il, it) }
            Whnf(newExpr, levelSubst)
        }

        is Expression.Lam -> {
            val left = this.typeExpr.inferSort(levelSubst, localCtx)
            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")
            val bodyTyWhnf = this.bodyExpr.inferType(levelSubst, listOf(this.typeExpr) + localCtx)
            val reifiedBodyTy = bodyTyWhnf.expr

            val newExpr = env.addCustomExpr {
                this.copyAsForAllE().copy(body = reifiedBodyTy.ie, ie = it)
            }
            Whnf(newExpr, bodyTyWhnf.levelSubst)
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
            check(this.typeExpr.isDefEq(valueTyWhnf.expr, levelSubst, valueTyWhnf.levelSubst)) {
                "Let value type mismatch in ${this.toStringDetailed()}: expected ${this.typeExpr.toStringDetailed()}, got ${valueTyWhnf.expr.toStringDetailed()}"
            }

            val bodyTyWhnf = this.bodyExpr.inferType(levelSubst, listOf(this.typeExpr) + localCtx)
            val instantiatedBodyTy = bodyTyWhnf.expr.applySubst(listOf(this.valueExpr))
            Whnf(instantiatedBodyTy, bodyTyWhnf.levelSubst)
        }

        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.StrVal -> TODO()
    }
}

context(env: Environment)
fun Expression.reduce(levelSubst: Map<Int, Level> = emptyMap()): Whnf {
    println("trying to reduce ${this.toStringDetailed()}")
    return when (this) {
        is Expression.App -> {
            val fnWhnf = this.fnExpr.reduce(levelSubst = levelSubst)
            when (val f = fnWhnf.expr) {
                is Expression.Lam ->
                    // beta; substitutions are applied eagerly
                    f.bodyExpr.applySubst(listOf(this.argExpr)).reduce(fnWhnf.levelSubst)

                else -> {
                    if (f == this.fnExpr) {
                        Whnf(this, fnWhnf.levelSubst)
                    } else {
                        val newExpr = env.addCustomExpr { this.copy(fn = f.ie, ie = it) }
                        Whnf(newExpr, fnWhnf.levelSubst)
                    }
                }
            }
        }

        is Expression.Lam -> Whnf(this, levelSubst)
        is Expression.Bvar -> Whnf(this, levelSubst)
        is Expression.Const -> {
            val constLevelSubst = composeLevelSubst(levelSubst, this.levelSubstMap())
            when (val d = decl) {
                is Declaration.Def -> d.valueExpr.reduce(constLevelSubst)
                else -> Whnf(this, constLevelSubst)
            }
        }

        is Expression.ForallE -> Whnf(this, levelSubst)
        is Expression.Sort -> Whnf(this, levelSubst)
        is Expression.LetE -> this.bodyExpr.applySubst(listOf(this.valueExpr)).reduce(levelSubst)
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.StrVal -> TODO()
    }
}

context(env: Environment)
private fun Expression.inferSort(
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
private fun Level.instantiateLevelParams(subst: Map<Int, Level>): Level {
    return when (this) {
        Level.Zero -> this
        is Level.Param -> subst[this.il] ?: this
        is Level.Succ -> {
            val newLevel = this.level.instantiateLevelParams(subst)
            if (newLevel == this.level) {
                this
            } else {
                env.addCustomLevel { Level.Succ(newLevel.il, it) }
            }
        }

        is Level.Max -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                env.addCustomLevel { Level.Max(listOf(newLeft.il, newRight.il), it) }
            }
        }

        is Level.Imax -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                env.addCustomLevel { Level.Imax(listOf(newLeft.il, newRight.il), it) }
            }
        }
    }
}

context(env: Environment)
private fun composeLevelSubst(outer: Map<Int, Level>, inner: Map<Int, Level>): Map<Int, Level> {
    if (inner.isEmpty()) return outer
    if (outer.isEmpty()) return inner
    val normalizedInner = inner.mapValues { it.value.instantiateLevelParams(outer) }
    return outer + normalizedInner
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

        else -> this
    }
}

context(env: Environment)
private fun Expression.Const.levelSubstMap(): Map<Int, Level> {
    val params = this.decl.levelParams
    check(params.size == this.levels.size) {
        "Universe argument mismatch for ${this.toStringDetailed()}: expected ${params.size}, got ${this.levels.size}"
    }
    return params.indices.associate { index ->
        params[index].il to this.levels[index]
    }
}