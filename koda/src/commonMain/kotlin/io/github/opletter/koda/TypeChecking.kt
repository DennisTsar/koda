package io.github.opletter.koda

import kotlin.math.max


class Environment {
    val names: MutableMap<Int, Name> = mutableMapOf()
    val declarations: MutableMap<Int, Declaration> = mutableMapOf()
    val expressions: MutableMap<Int, Expression> = mutableMapOf()
    val levels: MutableMap<Int, Level> = mutableMapOf(0 to Level.Zero)

    val declTypeByName: MutableMap<Int, Int> = mutableMapOf()

    val openBinders: MutableList<Int> = mutableListOf()

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\nDeclarations:\n${declarations.toList().joinToString("\n")}" +
                "\n\nExpressions:\n${expressions.toList().joinToString("\n")}\n\nLevels:\n${levels.toList().joinToString("\n")}"
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
                env.names[data.in2] = data
            }
            is Level -> {
                // TODO: these checks are just for debugging
                check(data.il != 0) { "Level 0 is assumed" }
                check(data.il !in env.levels) { "Duplicate level ${data.il}" }
                env.levels[data.il] = data
            }
            is Expression -> {
                env.expressions[data.ie] = data
            }
            is Declaration -> {
                // (1): "the declaration is not already declared in the environment"
                val name = env.names[data.name] ?: error("Name not found for ${data.name}")
                name as? Name.Str ?: error("Expected Str name, got ${name::class.simpleName}")
                val oldDecl = env.declarations.put(name.in2, data)
                check(oldDecl == null) { "Duplicate declaration for ${name.str}" }
                // (2): "has no duplicate universe parameters"
                // TODO
                // (3): "the declaration's type is actually a type and not a value (that infer declar.ty returns an expression Sort <n>)"
                // TODO
                val typeExpr = env.expressions[data.type] ?: error("Type expression not found for ${data.name}")
//                val inferredType = typeExpr.inferType()
                println("found type: $typeExpr")

                // TODO: this is probably wrong, need to do inference
//                check(typeExpr is Expression.Sort) { "Expected Sort type, got ${typeExpr::class.simpleName}" }

                when (data) {
                    is Declaration.Axiom -> TODO()
                    is Declaration.Def -> {
                        val valueExpr = env.expressions[data.value] ?: error("Value expression not found for ${data.name}")
                        println("found value: $valueExpr")
                        val typeType = typeExpr.inferType()
                        val valueType = valueExpr.inferType()
                        check(typeType == valueType + 1) { "Type ($typeType) should be value ($valueType) + 1" }
                        env.declTypeByName[data.name] = typeType
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
fun Expression.inferType(): Int = when (this) {
    is Expression.App -> {
        // TODO: validate that the arg has the correct type
        val decl = env.expressions[this.fn] ?: error("Expression not found for ${this.fn}")
        decl.inferType()
    }
    is Expression.Bvar -> {
        // TODO
        println("looking for type of bvar $this")
//        val binderType = env.openBinders.removeLastOrNull() ?: error("No open binders found for bvar $this")
//        println("found type of bvar $this: $binderType")
        val bvarTypeExpr =  env.expressions[this.bvar]
        bvarTypeExpr?.inferType()?.minus(1) ?: error("Type expression not found for ${this.bvar}")
//        env.levels[env.expressions[this.bvar]]?.inferType() ?: error("Level ${this.bvar} not found")
    }
    is Expression.Const -> env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
    is Expression.ForallE -> {
//        val left = env.declarations[this.type] ?: error("Declaration not found for ${this.type}")
        val leftType = env.expressions[this.type]?.inferType() ?: error("Type expression not found for ${this.name}")
        val right = env.expressions[this.body] ?: error("Body expression not found for ${this.name}")
//        env.openBinders.add(leftType - 1) // idk what I'm doing
        val rightType = right.inferType()
        println("Calculated type for $this: imax($leftType, $rightType)")
        // TODO: I tried to ruse the existing logic for imax, but that looks things up in the env,
        //  which obviously doesn't exist since we just made this up. Should I add something to the env here?
//        Level.Imax(listOf(leftType, rightType), -1).inferType()
        val level = if (rightType == 0) 0 else max(leftType, rightType)
        level
    }
    is Expression.Lam -> {
        val inferredType = env.expressions[this.type]?.inferType() ?: error("Type expression not found for ${this.name}")
        // TODO: assert! infersAsSort(binder.type)

        // TODO (2): this should delegate to pi/forallE logic
        // TODO: this "- 1" is majorly wrong but is supposed to represent instantiation or something (we start with Type -> Type, then pass in a Type, so we're left with just Type)
        val leftType = env.expressions[this.type]?.inferType()?.minus(1) ?: error("Type expression not found for ${this.name}")
        val right = env.expressions[this.body] ?: error("Body expression not found for ${this.name}")
//        env.openBinders.add(leftType - 1) // idk what I'm doing
        println("calculating type for body of $this: $body")
        val rightType = right.inferType()
        println("Calculated type for $this: imax($leftType, $rightType)")
        // TODO: I tried to ruse the existing logic for imax, but that looks things up in the env,
        //  which obviously doesn't exist since we just made this up. Should I add something to the env here?
//        Level.Imax(listOf(leftType, rightType), -1).inferType()
        val level = if (rightType == 0) 0 else max(leftType, rightType)
        level
    }
    is Expression.LetE -> TODO()
    is Expression.Mdata -> TODO()
    is Expression.NatVal -> TODO()
    is Expression.Proj -> TODO()
    is Expression.Sort ->
        env.levels[this.sort]?.inferType()?.plus(1) ?: error("Level ${this.sort} not found") // TODO: i just made up this ?.plus(1)
    is Expression.StrVal -> TODO()
}

context(env: Environment)
fun Level.inferType(): Int = when (this) {
    Level.Zero -> 0
    is Level.Imax -> env.levels[this.imax[1]]?.inferType()?.let { right ->
        if (right == 0) 0 else max(
            right,
            env.levels[this.imax[0]]?.inferType() ?: error("Level ${this.imax[0]} not found")
        )
    } ?: error("Level ${this.imax[1]} not found")

    is Level.Max -> max(
        env.levels[this.max[0]]?.inferType() ?: error("Level ${this.max[0]} not found"),
        env.levels[this.max[1]]?.inferType() ?: error("Level ${this.max[1]} not found")
    )
    is Level.Param -> env.levels[this.param]?.inferType() ?: error("Level ${this.param} not found")
    is Level.Succ -> env.levels[this.succ]?.inferType()?.plus(1) ?: error("Level ${this.succ} not found")
}