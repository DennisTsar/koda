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
        val newLevel = exprConstructor(nextExprIndex)
        expressions[nextExprIndex] = newLevel
        return nextExprIndex
    }

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\nDeclarations:\n${
            declarations.toList().joinToString("\n")
        }" +
                "\n\nExpressions:\n${expressions.toList().joinToString("\n")}\n\nLevels:\n${
                    levels.toList().joinToString("\n")
                }"
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
                // TODO
                val typeExpr = data.typeExpr.reduce().expr
//                val inferredType = typeExpr.inferType()
                println("found type: ${typeExpr.toStringDetailed()}")

                // TODO: this is probably wrong, need to do inference
//                check(typeExpr is Expression.Sort) { "Expected Sort type, got ${typeExpr::class.simpleName}" }

                when (data) {
                    is Declaration.Axiom -> TODO()
                    is Declaration.Def -> {
                        val value = data.valueExpr
                        println("found value: ${value.toStringDetailed()}")
                        val inferredValueType = value.inferType().expr
                        println("inferred type of value: ${inferredValueType.toStringDetailed()}")
                        check(data.typeExpr.isDefEq(inferredValueType)) { "value not defeq to type for $data" }
                        env.declTypeByName[data.name] = data.typeExpr
                    }

                    is Declaration.Opaque -> TODO()
                    is Declaration.Quot -> TODO()
                    is Declaration.Thm -> TODO()
                }

                // (4): "the declaration's type has no free variables"
                // TODO
            }

            else -> {}
        }
    }
}

context(env: Environment)
fun Expression.isDefEq(other: Expression): Boolean {
    return when (this) {
        is Expression.App if other is Expression.App -> fnExpr.isDefEq(other.fnExpr) && argExpr.isDefEq(other.argExpr)
        is Expression.App -> this.reduce().expr.also { println("reduced to: ${it.toStringDetailed()}") }.isDefEq(other)
        is Expression.Bvar if other is Expression.Bvar -> this.bvar == other.bvar
        is Expression.Bvar -> TODO()//false
        is Expression.Const if other is Expression.Const ->
            this.name == other.name && this.levels.size == other.levels.size
                    && this.levels.zip(other.levels).all { (l1, l2) -> l1.isEqual(l2) }

        is Expression.ForallE if other is Expression.ForallE -> {
            typeExpr.isDefEq(other.typeExpr) && withOpenBinder(typeExpr) { bodyExpr.isDefEq(other.bodyExpr) }
        }

        is Expression.Lam if other is Expression.Lam -> {
            typeExpr.isDefEq(other.typeExpr) && withOpenBinder(typeExpr) { bodyExpr.isDefEq(other.bodyExpr) }
        }

        is Expression.LetE if other is Expression.LetE -> TODO()
        is Expression.Mdata if other is Expression.Mdata -> TODO()
        is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
        is Expression.Proj if other is Expression.Proj -> TODO()
        is Expression.Sort if other is Expression.Sort -> this.level.isEqual(other.level)
        is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
        else -> TODO("DefEq not implemented for ${this::class.simpleName} and ${other::class.simpleName}")
    }
}

data class Whnf(val expr: Expression, val env: List<Expression>)

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
private fun inferSortOf(expr: Expression, subst: List<Expression> = emptyList()): Level {
    val tyWhnf = expr.inferType(subst)
    val whnfTy = tyWhnf.expr.reduce(tyWhnf.env)
    val sort = whnfTy.expr as? Expression.Sort
        ?: error("Expected Sort type for ${expr.toStringDetailed()}, got ${whnfTy.expr.toStringDetailed()}")
    return sort.level
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
fun Expression.inferType(subst: List<Expression> = emptyList()): Whnf {
    return when (this) {
        is Expression.App -> {
            val fnTyWhnf = this.fnExpr.inferType(subst)
            when (val fnTy = fnTyWhnf.expr) {
                is Expression.ForallE -> {
                    // dependent instantiation, delayed via env
                    Whnf(fnTy.bodyExpr, listOf(this.argExpr) + fnTyWhnf.env)
                }

                else -> error("Expected function type for app ${this.toStringDetailed()}, got ${fnTy.toStringDetailed()}")
            }
        }

        is Expression.Bvar -> {
            if (this.bvar < env.openBinders.size) {
                // live binder: stored type is in the outer context, so lift it
                // back under the current number of live binders.
                Whnf(env.openBinders[this.bvar].lift(this.bvar + 1), subst)
            } else {
                // delayed substitution from consumed binders
                val j = this.bvar - env.openBinders.size
                val arg = subst.getOrNull(j)
                    ?: error("Unbound bvar ${this.bvar} in ${this.toStringDetailed()}")
                arg.inferType()
            }
        }

        is Expression.Const -> {
            val ty = env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
            Whnf(ty, subst)
        }

        is Expression.ForallE -> {
            val left = inferSortOf(this.typeExpr, subst)
            println("calculated left level for ${this.toStringDetailed()}: ${left.toStringDetailed()}")

            val right = withOpenBinder(this.typeExpr) { inferSortOf(this.bodyExpr, subst) }

            val newLevel = env.addCustomLevel {
                val leftIndex = env.levels.entries.find { it.value == left }?.key
                    ?: error("Level not found for $left")
                val rightIndex = env.levels.entries.find { it.value == right }?.key
                    ?: error("Level not found for $right")
                Level.Imax(listOf(leftIndex, rightIndex), it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel, it) }
            Whnf(env.expressions[newExpr] ?: error("Expression not found for $newExpr"), subst)
        }

        is Expression.Lam -> {
            val bodyTyWhnf = withOpenBinder(this.typeExpr) { this.bodyExpr.inferType(subst) }

            val newExpr = env.addCustomExpr {
                this.copyAsForAllE().copy(
                    body = bodyTyWhnf.expr.ie,
                    ie = it
                )
            }
            Whnf(env.expressions[newExpr] ?: error("Expression not found for $newExpr"), bodyTyWhnf.env)
        }

        is Expression.Sort -> {
            val newLevel = env.addCustomLevel {
                val indexOfLevel = env.levels.entries.find { it.value == this.level }?.key
                    ?: error("Level not found for ${this.level}")
                Level.Succ(indexOfLevel, it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel, it) }
            Whnf(env.expressions[newExpr] ?: error("Expression not found for $newExpr"), subst)
        }

        is Expression.LetE -> TODO()
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.StrVal -> TODO()
    }
}

context(env: Environment)
fun Expression.reduce(subst: List<Expression> = emptyList()): Whnf {
    println("trying to reduce ${this.toStringDetailed()} (with subts= ${subst.joinToString { it.toStringDetailed() }})")
    return when (this) {
        is Expression.App -> {
            val fnWhnf = this.fnExpr.reduce(subst)
            when (val f = fnWhnf.expr) {
                is Expression.Lam ->
                    // beta, delayed via subst list
                    f.bodyExpr.reduce(listOf(this.argExpr) + fnWhnf.env)

                else -> Whnf(this, subst)
            }
        }

        is Expression.Lam -> Whnf(this, subst)

        is Expression.Bvar -> {
            val arg = subst.getOrNull(this.bvar)
            if (arg != null) Whnf(arg, emptyList()) else Whnf(this, subst)
        }

        is Expression.Const -> {
            when (val d = decl) {
                is Declaration.Def -> Whnf(d.valueExpr, subst)
                else -> TODO()//Whnf(this, subst)
            }
        }

        is Expression.ForallE -> Whnf(this, subst)
        is Expression.Sort -> Whnf(this, subst)

        is Expression.LetE -> TODO()
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.StrVal -> TODO()
    }
}


//context(env: Environment)
//fun Level.isEqual(other: Level): Boolean {
//    return when (this) {
//        is Level.Zero -> other is Level.Zero
//        is Level.Succ if other is Level.Succ -> this.level.isEqual(other.level)
//        is Level.Succ if other is Level.Imax -> {
//            val rightIsZero = other.isEqual(Level.Zero)
//            false
//        }
//        is Level.Max -> TODO()
//        is Level.Imax -> TODO()
//        else -> TODO("isEqual not implemented for ${this::class.simpleName} ${other::class.simpleName}")
//    }
//}
//
//
//context(env: Environment)
//fun Level.isLessOrEqual(other: Level): Boolean {
//    return when (this) {
//        is Level.Zero -> other is Level.Zero
//        is Level.Succ if other is Level.Succ -> this.level.isEqual(other.level)
//        is Level.Succ if other is Level.Imax -> {
//            val rightIsZero = other.isEqual(Level.Zero)
//            false
//        }
//        is Level.Max -> TODO()
//        is Level.Imax -> TODO()
//        else -> TODO("isEqual not implemented for ${this::class.simpleName} ${other::class.simpleName}")
//    }
//}

context(env: Environment)
fun Level.isEqual(other: Level): Boolean = this.isLessOrEqual(other) && other.isLessOrEqual(this)

context(env: Environment)
fun Level.isLessOrEqual(other: Level, balance: Int = 0): Boolean = when (this) {
    is Level.Zero if balance >= 0 -> true
    is Level.Zero if other is Level.Imax -> true
    // I added this next one
    is Level.Imax if this.right.isEqual(Level.Zero) -> Level.Zero.isLessOrEqual(other, balance)
    // I added this next one
//    is Level.Succ if other is Level.Zero -> false
    else if other is Level.Zero && balance < 0 -> false
    is Level.Param if other is Level.Param -> this.name == other.name && balance >= 0
    is Level.Param if other is Level.Zero -> false
    is Level.Zero if other is Level.Param -> balance >= 0
    is Level.Succ -> this.level.isLessOrEqual(other, balance - 1)
    else if other is Level.Succ -> this.isLessOrEqual(other.level, balance + 1)
    is Level.Max -> this.left.isLessOrEqual(other, balance) && this.right.isLessOrEqual(other, balance)
//    is Level.Param, is Level.Zero if other is Level.Max -> // illegal syntax
    is Level.Param if other is Level.Max -> this.isLessOrEqual(other.left, balance) || this.isLessOrEqual(other.right, balance)
    is Level.Zero if other is Level.Max -> this.isLessOrEqual(other.left, balance) || this.isLessOrEqual(other.right, balance)
    is Level.Imax if this.right is Level.Param -> TODO()
    else if other is Level.Imax && other.right is Level.Param -> TODO()
    is Level.Imax if other is Level.Imax -> balance >= 0 && this.left.isEqual(other.left) && this.right.isEqual(other.right)
    is Level.Imax if this.right is Level.Imax -> TODO()
    is Level.Imax if this.right is Level.Max -> TODO()
    else if other is Level.Imax && other.right is Level.Imax -> TODO()
    else if other is Level.Imax && other.right is Level.Max -> TODO()
    // TODO: is this case not handled in the sample implementation or? TODO: balance?
    is Level.Imax -> {
        if (this.left.isLessOrEqual(Level.Zero, balance))
            this.left.isLessOrEqual(other, balance)
        else {
//            TODO()
            val custom = env.addCustomLevel { Level.Max(listOf(env.findLevelFor(this.left), env.findLevelFor(this.right)), it) }
            env.levels[custom]!!.isLessOrEqual(other, balance)
        }
    }
//    is Level.Imax -> error("unexpected unhandled case: $this $other")
    Level.Zero -> error("unexpected unhandled case: $this $other $balance")
    is Level.Param -> error("unexpected unhandled case: $this $other $balance")
}

fun Environment.findLevelFor(i: Level): Int {
    return buildMap { putAll(this@findLevelFor.levels) }.entries.find {
        it.value.isEqual(i)
    }?.key ?: error("Level $i not found")
}