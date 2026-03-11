package io.github.opletter.koda


class Environment {
    val names: MutableMap<Int, Name> = mutableMapOf()
    val declarations: MutableMap<Int, Declaration> = mutableMapOf()
    val expressions: MutableMap<Int, Expression> = mutableMapOf()
    val levels: MutableMap<Int, Level> = mutableMapOf(0 to Level.Zero)

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()

    val openBinders: MutableList<Int> = mutableListOf()

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
                // TODO
                // (3): "the declaration's type is actually a type and not a value (that infer declar.ty returns an expression Sort <n>)"
                // TODO
                val typeExpr = data.typeExpr.reduce()
//                val inferredType = typeExpr.inferType()
                println("found type: ${typeExpr.toStringDetailed()}")

                // TODO: this is probably wrong, need to do inference
//                check(typeExpr is Expression.Sort) { "Expected Sort type, got ${typeExpr::class.simpleName}" }

                when (data) {
                    is Declaration.Axiom -> TODO()
                    is Declaration.Def -> {
                        val value = data.valueExpr
                        println("found value: ${value.toStringDetailed()}")
                        val inferredValueType = value.inferType()
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
        is Expression.App -> this.reduce().isDefEq(other)
        is Expression.Bvar if other is Expression.Bvar -> this.expr.isDefEq(other.expr)
        is Expression.Bvar -> this.expr.isDefEq(other)
        is Expression.Const if other is Expression.Const ->
            this.name == other.name && this.levels.size == other.levels.size
                    && this.levels.zip(other.levels).all { (l1, l2) -> l1.isEqual(l2) }

        is Expression.ForallE if other is Expression.ForallE ->
            typeExpr.isDefEq(other.typeExpr) && bodyExpr.isDefEq(other.bodyExpr) // TODO: should do fvar substitution
        is Expression.Lam if other is Expression.Lam -> typeExpr.isDefEq(other.typeExpr) && bodyExpr.isDefEq(other.bodyExpr) // TODO: should do fvar substitution
        is Expression.LetE if other is Expression.LetE -> TODO()
        is Expression.Mdata if other is Expression.Mdata -> TODO()
        is Expression.NatVal if other is Expression.NatVal -> this.natVal == other.natVal
        is Expression.Proj if other is Expression.Proj -> TODO()
        is Expression.Sort if other is Expression.Sort -> this.level.isEqual(other.level)
        is Expression.StrVal if other is Expression.StrVal -> this.strVal == other.strVal
        else -> TODO("DefEq not implemented for ${this::class.simpleName} and ${other::class.simpleName}")
    }
}

context(env: Environment)
fun Expression.inferType(): Expression {
    return when (this) {
        is Expression.App -> this.fnExpr.inferType() // TODO: validate that the arg has the correct type
        is Expression.Bvar -> {
            val expr = this.expr
            if (expr is Expression.ForallE) expr.bodyExpr else expr
        }
        is Expression.Const -> env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
        is Expression.ForallE -> {
            val left = (typeExpr as? Expression.Sort)?.level ?: error("Expected Sort type for ${this.typeExpr}, got ${this.typeExpr::class.simpleName}")
            val right = (bodyExpr.inferType() as? Expression.Sort)?.level ?: error("Expected Sort type for ${this.bodyExpr.inferType()}, got ${this.bodyExpr.inferType()::class.simpleName}")
//                if (bodyExpr is Expression.Bvar) left else (bodyExpr.inferType() as? Expression.Sort)?.level ?: error("Expected Sort type for ${this.bodyExpr.inferType()}, got ${this.bodyExpr.inferType()::class.simpleName}")
            val newLevel = env.addCustomLevel {
                val leftIndex = env.levels.entries.find { it.value ==left }?.key
                    ?: error("Level not found for $left")
                val rightIndex = env.levels.entries.find { it.value == right }?.key
                    ?: error("Level not found for $right")
                Level.Imax(listOf(leftIndex, rightIndex), it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel, it) }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }
        is Expression.Lam -> {
//            val left = (typeExpr as? Expression.Sort) ?: error("Expected Sort type for ${this.typeExpr}, got ${this.typeExpr::class.simpleName}")
            val right = bodyExpr.inferType()
//                if (bodyExpr is Expression.Bvar) left else (bodyExpr.inferType() as? Expression.Sort) ?: error("Expected Sort type for ${this.bodyExpr}")
            val newExpr = env.addCustomExpr {
                this.copyAsForAllE().copy(
                    body = env.expressions.entries.find { it.value == right }?.key ?: error("Expression not found for ${this.bodyExpr}"),
                    ie = it
                )
            }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }
        is Expression.LetE -> TODO()
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.Sort -> {
            val newLevel = env.addCustomLevel {
                val indexOfLevel = env.levels.entries.find { it.value == this.level }?.key
                    ?: error("Level not found for ${this.level}")
                Level.Succ(indexOfLevel, it)
            }
            val newExpr = env.addCustomExpr { Expression.Sort(newLevel, it) }
            env.expressions[newExpr] ?: error("Expression not found for $newExpr")
        }

        is Expression.StrVal -> TODO()
    }
}


context(env: Environment)
fun Expression.reduce(): Expression {
    return when (this) {
        is Expression.App -> {
            val declType = this.fnExpr.reduce()
//            println("decl type for ${x.name}: ${declType.toStringDetailed()}")
//            println("found app:\nfnExpr: ${this.fnExpr.toStringDetailed()}\nargExpr: ${this.argExpr.toStringDetailed()}")
            if (declType is Expression.ForallE) declType.bodyExpr else TODO()
        }
        is Expression.Bvar -> TODO()
        is Expression.Const -> env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
        is Expression.ForallE -> this
        is Expression.Lam -> this
        is Expression.LetE -> TODO()
        is Expression.Mdata -> TODO()
        is Expression.NatVal -> TODO()
        is Expression.Proj -> TODO()
        is Expression.Sort -> this

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