package io.github.opletter.koda


class Environment {
    val names: MutableMap<Int, Name> = mutableMapOf()
    val declarations: MutableMap<Int, Declaration> = mutableMapOf()
    val expressions: MutableMap<Int, Expression> = mutableMapOf()
    val levels: MutableMap<Int, Level> = mutableMapOf(0 to Level.Zero)

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()

    val openBinders: MutableList<Expression> = mutableListOf()

    private var nextLevelIndex: Int = 0

    fun addCustomLevel(levelConstructor: (Int) -> Level): Int {
        nextLevelIndex--
        val newLevel = levelConstructor(nextLevelIndex)
        levels[nextLevelIndex] = newLevel
        return nextLevelIndex
    }

    private var nextExprIndex: Int = -100 // Could start with 0, but this helps while debugging vs levels

    fun addCustomExpr(exprConstructor: (Int) -> Expression): Int {
        nextExprIndex--
        val newExpr = exprConstructor(nextExprIndex)
        expressions[nextExprIndex] = newExpr
        return nextExprIndex
    }

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\n" +
                "Declarations:\n${declarations.toList().joinToString("\n")}\n\n" +
                "Expressions:\n${expressions.toList().joinToString("\n")}\n\n" +
                "Levels:\n${levels.toList().joinToString("\n")}"
    }
}

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
                val typeWhnf = data.typeExpr.reduce()
                println("found type: ${typeWhnf.expr.toStringDetailed()}")
                val declaredTyTy = data.typeExpr.inferType()
                val declaredTyTyWhnf = declaredTyTy.expr.reduce(declaredTyTy.env, declaredTyTy.levelSubst)
                check(declaredTyTyWhnf.expr is Expression.Sort) {
                    "The type of a declaration has to be a type, not some other expression"
                }

                when (data) {
                    is Declaration.Axiom -> TODO()
                    is Declaration.Def -> {
                        check(typeCheckDeclaration(data.valueExpr, typeWhnf)) {
                            "value not defeq to type for $data"
                        }
                    }

                    is Declaration.Opaque -> TODO()
                    is Declaration.Quot -> TODO()
                    is Declaration.Thm -> {
                        check(typeCheckDeclaration(data.valueExpr, typeWhnf)) {
                            "value not defeq to type for $data"
                        }
                        val theoremTySort = declaredTyTyWhnf.expr as Expression.Sort
                        val theoremTyLevel = theoremTySort.level.instantiateLevelParams(declaredTyTyWhnf.levelSubst)
                        check(theoremTyLevel.isLessOrEqual(Level.Zero)) {
                            "The type of a theorem has to be a proposition: found ${declaredTyTyWhnf.expr.toStringDetailed()}"
                        }
                    }
                }

                env.declTypeByName[data.name] = typeWhnf.expr

                // (4): "the declaration's type has no free variables"
                // TODO
            }

            else -> {}
        }
    }
}

context(env: Environment)
fun typeCheckDeclaration(value: Expression, typeWhnf: Whnf) : Boolean {
    println("found value: ${value.toStringDetailed()}")
    val inferredValueType = value.inferType()
    println("inferred type of value: ${inferredValueType.expr.toStringDetailed()}")
    val expectedType = typeWhnf.expr.applySubst(typeWhnf.env)
    val actualType = inferredValueType.expr.applySubst(inferredValueType.env)
    return expectedType.isDefEq(actualType, typeWhnf.levelSubst, inferredValueType.levelSubst)
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
                    withOpenBinder(this.typeExpr) {
                        this.bodyExpr.isDefEq(other.bodyExpr, levelSubstLeft, levelSubstRight)
                    }
        }

        is Expression.Lam if other is Expression.Lam -> {
            this.typeExpr.isDefEq(other.typeExpr, levelSubstLeft, levelSubstRight) &&
                    withOpenBinder(this.typeExpr) {
                        this.bodyExpr.isDefEq(other.bodyExpr, levelSubstLeft, levelSubstRight)
                    }
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

context(env: Environment)
private fun Expression.Const.levelSubstMap(): Map<Int, Level> {
    val params = this.decl.levelParams
    check(params.size == this.levels.size) {
        "Universe argument mismatch for ${this.toStringDetailed()}: expected ${params.size}, got ${this.levels.size}"
    }
    return params.indices.associate { index ->
        val param = params[index] as? Level.Param
            ?: error("Declaration level parameter is not a param for ${this.toStringDetailed()}")
        param.il to this.levels[index]
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
                val newIndex = env.addCustomLevel { Level.Succ(newLevel.il, it) }
                env.levels[newIndex] ?: error("Level not found for $newIndex")
            }
        }

        is Level.Max -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                val newIndex = env.addCustomLevel { Level.Max(listOf(newLeft.il, newRight.il), it) }
                env.levels[newIndex] ?: error("Level not found for $newIndex")
            }
        }

        is Level.Imax -> {
            val newLeft = this.left.instantiateLevelParams(subst)
            val newRight = this.right.instantiateLevelParams(subst)
            if (newLeft == this.left && newRight == this.right) {
                this
            } else {
                val newIndex = env.addCustomLevel { Level.Imax(listOf(newLeft.il, newRight.il), it) }
                env.levels[newIndex] ?: error("Level not found for $newIndex")
            }
        }
    }
}

context(env: Environment)
private fun composeLevelSubst(outer: Map<Int, Level>, inner: Map<Int, Level>): Map<Int, Level> {
    if (inner.isEmpty()) return outer
    if (outer.isEmpty()) return inner
    val normalizedInner = inner.mapValues { entry -> entry.value.instantiateLevelParams(outer) }
    return outer + normalizedInner
}

context(env: Environment)
fun Expression.applySubst(subst: List<Expression>, depth: Int = 0): Expression {
    return when (this) {
        is Expression.Bvar -> when {
            this.bvar < depth -> this
            this.bvar - depth < subst.size -> subst[this.bvar - depth].lift(depth)
            subst.isEmpty() -> this
            else -> {
                val newExpr = env.addCustomExpr {
                    this.copy(bvar = this.bvar - subst.size, ie = it)
                }
                env.expressions[newExpr] ?: error("Expression not found for $newExpr")
            }
        }

        is Expression.App -> {
            val newFn = this.fnExpr.applySubst(subst, depth)
            val newArg = this.argExpr.applySubst(subst, depth)
            val newExpr = env.addCustomExpr {
                this.copy(fn = newFn.ie, arg = newArg.ie, ie = it)
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        is Expression.ForallE -> {
            val newType = this.typeExpr.applySubst(subst, depth)
            val newBody = this.bodyExpr.applySubst(subst, depth + 1)
            val newExpr = env.addCustomExpr {
                this.copy(type = newType.ie, body = newBody.ie, ie = it)
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        is Expression.Lam -> {
            val newType = this.typeExpr.applySubst(subst, depth)
            val newBody = this.bodyExpr.applySubst(subst, depth + 1)
            val newExpr = env.addCustomExpr {
                this.copy(type = newType.ie, body = newBody.ie, ie = it)
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        else -> this
    }
}

data class Whnf(
    val expr: Expression,
    val env: List<Expression>,
    val levelSubst: Map<Int, Level> = emptyMap(),
)

context(env: Environment)
private inline fun <T> withOpenBinder(typeExpr: Expression, block: () -> T): T {
    env.openBinders.add(0, typeExpr) // nearest binder first
    try {
        return block()
    } finally {
        env.openBinders.removeFirst()
    }
}

context(env: Environment)
private fun inferSortOf(
    expr: Expression,
    subst: List<Expression> = emptyList(),
    levelSubst: Map<Int, Level> = emptyMap(),
): Level {
    val tyWhnf = expr.inferType(subst, levelSubst)
    val whnfTy = tyWhnf.expr.reduce(tyWhnf.env, tyWhnf.levelSubst)
    val sort = whnfTy.expr as? Expression.Sort
        ?: error("Expected Sort type for ${expr.toStringDetailed()}, got ${whnfTy.expr.toStringDetailed()}")
    return sort.level.instantiateLevelParams(whnfTy.levelSubst)
}

context(env: Environment)
fun Expression.lift(amount: Int = 1, cutoff: Int = 0): Expression {
    return when (this) {
        is Expression.Bvar -> {
            if (this.bvar >= cutoff) {
                val newExpr = env.addCustomExpr {
                    this.copy(bvar = this.bvar + amount, ie = it)
                }
                env.expressions[newExpr] ?: error("Expression not found for $newExpr")
            } else {
                this
            }
        }

        is Expression.App -> {
            val newFn = this.fnExpr.lift(amount, cutoff)
            val newArg = this.argExpr.lift(amount, cutoff)
            val newExpr = env.addCustomExpr {
                this.copy(fn = newFn.ie, arg = newArg.ie, ie = it)
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        is Expression.ForallE -> {
            val newType = this.typeExpr.lift(amount, cutoff)
            val newBody = this.bodyExpr.lift(amount, cutoff + 1)
            val newExpr = env.addCustomExpr {
                this.copy(type = newType.ie, body = newBody.ie, ie = it)
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        is Expression.Lam -> {
            val newType = this.typeExpr.lift(amount, cutoff)
            val newBody = this.bodyExpr.lift(amount, cutoff + 1)
            val newExpr = env.addCustomExpr {
                this.copy(type = newType.ie, body = newBody.ie, ie = it)
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        else -> this
    }
}

context(env: Environment)
fun Expression.inferType(
    subst: List<Expression> = emptyList(),
    levelSubst: Map<Int, Level> = emptyMap(),
): Whnf {
    return when (this) {
        is Expression.App -> {
            val fnTy0 = this.fnExpr.inferType(subst, levelSubst)
            val fnTyWhnf = fnTy0.expr.reduce(fnTy0.env, fnTy0.levelSubst)
            when (val fnTy = fnTyWhnf.expr) {
                is Expression.ForallE -> {
                    val argTy0 = this.argExpr.inferType(subst, levelSubst)
                    val argTy = argTy0.expr.applySubst(argTy0.env)
                    val expectedArgTy = fnTy.typeExpr.applySubst(fnTyWhnf.env)
                    check(expectedArgTy.isDefEq(argTy, fnTyWhnf.levelSubst, argTy0.levelSubst)) {
                        "Application argument type mismatch in ${this.toStringDetailed()}: expected ${expectedArgTy.toStringDetailed()}, got ${argTy.toStringDetailed()}"
                    }
                    // dependent instantiation, delayed via env
                    Whnf(fnTy.bodyExpr, listOf(this.argExpr) + fnTyWhnf.env, fnTyWhnf.levelSubst)
                }

                else -> error("Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}")
            }
        }

        is Expression.Bvar -> {
            if (this.bvar < subst.size) {
                // innermost consumed binder
                subst[this.bvar].inferType(levelSubst = levelSubst)
            } else {
                val liveIndex = this.bvar - subst.size
                if (liveIndex < env.openBinders.size) {
                    // live binder: its stored type was recorded outside this binder,
                    // so lift it back under the current live-binder depth.
                    Whnf(env.openBinders[liveIndex].lift(liveIndex + 1), subst, levelSubst)
                } else {
                    error("Unbound bvar ${this.bvar} in ${this.toStringDetailed()}")
                }
            }
        }

        is Expression.Const -> {
            val ty = env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
            Whnf(ty, emptyList(), composeLevelSubst(levelSubst, this.levelSubstMap()))
        }

        is Expression.ForallE -> {
            val left = inferSortOf(this.typeExpr, subst, levelSubst)
            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")

            val right = withOpenBinder(this.typeExpr) { inferSortOf(this.bodyExpr, subst, levelSubst) }

            val newLevel = env.addCustomLevel {
                Level.Imax(listOf(left.il, right.il), it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel, it) }
            Whnf(env.expressions[newExpr] ?: error("Expression not found for $newExpr"), subst, levelSubst)
        }

        is Expression.Lam -> {
            val bodyTyWhnf = withOpenBinder(this.typeExpr) { this.bodyExpr.inferType(subst, levelSubst) }
            val reifiedBodyTy = bodyTyWhnf.expr.applySubst(bodyTyWhnf.env)

            val newExpr = env.addCustomExpr {
                this.copyAsForAllE().copy(
                    body = reifiedBodyTy.ie,
                    ie = it
                )
            }
            Whnf(
                env.expressions[newExpr] ?: error("Expression not found for $newExpr"),
                emptyList(),
                bodyTyWhnf.levelSubst
            )
        }

        is Expression.Sort -> {
            val normalizedLevel = this.level.instantiateLevelParams(levelSubst)
            val newLevel = env.addCustomLevel {
                Level.Succ(normalizedLevel.il, it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel, it) }
            Whnf(env.expressions[newExpr] ?: error("Expression not found for $newExpr"), subst, levelSubst)
        }

        is Expression.LetE -> TODO()
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.StrVal -> TODO()
    }
}

context(env: Environment)
fun Expression.reduce(
    subst: List<Expression> = emptyList(),
    levelSubst: Map<Int, Level> = emptyMap(),
): Whnf {
    if (subst.isNotEmpty()) {
        return this.applySubst(subst).reduce(levelSubst = levelSubst)
    }
    println("trying to reduce ${this.toStringDetailed()} (with subts= ${subst.joinToString { it.toStringDetailed() }})")
    return when (this) {
        is Expression.App -> {
            val fnWhnf = this.fnExpr.reduce(levelSubst = levelSubst)
            when (val f = fnWhnf.expr) {
                is Expression.Lam ->
                    // beta; substitutions are applied eagerly by reduce()
                    f.bodyExpr.reduce(listOf(this.argExpr), fnWhnf.levelSubst)

                else -> {
                    if (f == this.fnExpr) {
                        Whnf(this, emptyList(), fnWhnf.levelSubst)
                    } else {
                        val newExpr = env.addCustomExpr { this.copy(fn = f.ie, ie = it) }
                        Whnf(
                            env.expressions[newExpr] ?: error("Expression not found for $newExpr"),
                            emptyList(),
                            fnWhnf.levelSubst
                        )
                    }
                }
            }
        }

        is Expression.Lam -> Whnf(this, emptyList(), levelSubst)

        is Expression.Bvar -> Whnf(this, emptyList(), levelSubst)

        is Expression.Const -> {
            val constLevelSubst = composeLevelSubst(levelSubst, this.levelSubstMap())
            when (val d = decl) {
                is Declaration.Def -> {
                    d.valueExpr.reduce(emptyList(), constLevelSubst)
                }

                else -> Whnf(this, emptyList(), constLevelSubst)
            }
        }

        is Expression.ForallE -> Whnf(this, emptyList(), levelSubst)
        is Expression.Sort -> Whnf(this, emptyList(), levelSubst)

        is Expression.LetE -> TODO()
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.StrVal -> TODO()
    }
}

context(env: Environment)
fun Level.isEqual(other: Level): Boolean = this.isLessOrEqual(other) && other.isLessOrEqual(this)

context(env: Environment)
fun Level.isLessOrEqual(other: Level, balance: Int = 0): Boolean = when (this) {
    is Level.Zero if balance >= 0 -> true
    is Level.Zero if other is Level.Imax -> true
    else if other is Level.Zero && balance < 0 -> false
    is Level.Param if other is Level.Param -> this.name == other.name && balance >= 0
    is Level.Param if other is Level.Zero -> false
    is Level.Zero if other is Level.Param -> balance >= 0
    is Level.Succ -> this.level.isLessOrEqual(other, balance - 1)
    else if other is Level.Succ -> this.isLessOrEqual(other.level, balance + 1)
    is Level.Max -> this.left.isLessOrEqual(other, balance) && this.right.isLessOrEqual(other, balance)
//    is Level.Param, is Level.Zero if other is Level.Max -> // illegal syntax
    is Level.Param if other is Level.Max -> this.isLessOrEqual(other.left, balance)
            || this.isLessOrEqual(other.right, balance)

    is Level.Zero if other is Level.Max -> this.isLessOrEqual(other.left, balance)
            || this.isLessOrEqual(other.right, balance)

    is Level.Imax if this.right is Level.Param -> {
        compareByCases(this.right as Level.Param) { this.isLessOrEqual(other, balance) }
    }

    else if other is Level.Imax && other.right is Level.Param -> {
        compareByCases(other.right as Level.Param) { this.isLessOrEqual(other, balance) }
    }

    is Level.Imax if other is Level.Imax -> balance >= 0 && this.left.isEqual(other.left) && this.right.isEqual(other.right)
    is Level.Imax if this.right is Level.Imax -> {
        val customImax = env.addCustomLevel {
            Level.Imax(listOf(this.left.il, (this.right as Level.Imax).right.il), it)
        }
        val customMax = env.addCustomLevel { Level.Max(listOf(customImax, this.right.il), it) }
        env.levels[customMax]!!.isLessOrEqual(other, balance)
    }

    is Level.Imax if this.right is Level.Max -> TODO()
    else if other is Level.Imax && other.right is Level.Imax -> {
        val customImax = env.addCustomLevel {
            Level.Imax(listOf(other.left.il, (other.right as Level.Imax).right.il), it)
        }
        val customMax = env.addCustomLevel { Level.Max(listOf(customImax, other.right.il), it) }
        this.isLessOrEqual(env.levels[customMax]!!, balance)
    }

    else if other is Level.Imax && other.right is Level.Max -> TODO()
    else if (this != this.simplify() || other != other.simplify()) ->
        this.simplify().isLessOrEqual(other.simplify(), balance)

    Level.Zero, is Level.Imax, is Level.Param ->
        error("unexpected unhandled case: ${this.toStringDetailed()} ${other.toStringDetailed()} $balance")
}

context(env: Environment)
fun compareByCases(paramLevel: Level.Param, compare: () -> Boolean): Boolean {
    env.levels[paramLevel.il] = Level.Zero
    val caseZero = compare().also { env.levels[paramLevel.il] = paramLevel }
    val tempParamLevel = env.addCustomLevel { paramLevel.copy(il = it) }
    val succLevel = Level.Succ(tempParamLevel, paramLevel.il)
    env.levels[paramLevel.il] = succLevel
    val caseSucc = compare().also { env.levels[paramLevel.il] = paramLevel }
    return caseZero && caseSucc
}

context(env: Environment)
fun Level.simplify(): Level = when (this) {
    is Level.Imax if this.right.isEqual(Level.Zero) -> Level.Zero
    is Level.Imax if this.right is Level.Succ -> {
        val maxLevel = env.addCustomLevel {
            Level.Max(listOf(this.left.il, this.right.il), it)
        }
        env.levels[maxLevel]!!
    }

    else -> this
}