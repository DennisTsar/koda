package io.github.opletter.koda

import kotlin.math.max


class Environment {
    val names: MutableMap<Int, Name> = mutableMapOf()
    val declarations: MutableMap<Int, Declaration> = mutableMapOf()
    val expressions: MutableMap<Int, Expression> = mutableMapOf()
    val levels: MutableMap<Int, Level> = mutableMapOf(0 to Level.Zero)

    val declTypeByName: MutableMap<Name, Int> = mutableMapOf()

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
                val typeExpr = data.typeExpr
//                val inferredType = typeExpr.inferType()
                println("found type: $typeExpr")

                // TODO: this is probably wrong, need to do inference
//                check(typeExpr is Expression.Sort) { "Expected Sort type, got ${typeExpr::class.simpleName}" }

                when (data) {
                    is Declaration.Axiom -> TODO()
                    is Declaration.Def -> {
                        val valueExpr = data.valueExpr
                        println("found value: $valueExpr")
                        val typeType = typeExpr.inferType()
                        val valueType = valueExpr.inferType()
                        //(typeType == 0 && valueType == 0) ||
                        check(typeType == valueType + 1) { "Type (${typeType}) should be value (${valueType}) + 1" }
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
        val decl = this.fnExpr
        decl.inferType()
    }
    is Expression.Bvar -> {
        // TODO
        println("looking for type of bvar $this")
//        val binderType = env.openBinders.removeLastOrNull() ?: error("No open binders found for bvar $this")
//        println("found type of bvar $this: $binderType")
        val bvarTypeExpr = this.expr
        bvarTypeExpr.inferType() - 1
    }
    is Expression.Const -> env.declTypeByName[this.name] ?: error("Declaration not found for ${this.name}")
    is Expression.ForallE -> {
//        val left = env.declarations[this.type] ?: error("Declaration not found for ${this.type}")
        val leftType = this.typeExpr.inferType()
        val right = this.bodyExpr
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
        val inferredType = this.typeExpr.inferType()
        // TODO: assert! infersAsSort(binder.type)

        // TODO (2): this should delegate to pi/forallE logic
        // TODO: this "- 1" is majorly wrong but is supposed to represent instantiation or something (we start with Type -> Type, then pass in a Type, so we're left with just Type)
        val leftType = this.typeExpr.inferType() - 1
        val right = this.bodyExpr
//        env.openBinders.add(leftType - 1) // idk what I'm doing
        println("calculating type for body of $this: $bodyExpr")
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
    is Expression.Sort -> this.level.inferType() + 1
    is Expression.StrVal -> TODO()
}

context(env: Environment)
fun Level.inferType(): Int = when (this) {
    Level.Zero -> 0
    is Level.Imax -> this.right.inferType().let { right ->
        if (right == 0) 0 else max(right, this.left.inferType())
    }

    is Level.Max -> max(this.left.inferType(), this.right.inferType())
    is Level.Param -> TODO()//env.levels[this.param]?.inferType() ?: error("Level ${this.param} not found")
    is Level.Succ -> this.level.inferType() + 1
}