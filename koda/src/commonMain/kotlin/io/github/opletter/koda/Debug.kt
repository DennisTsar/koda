package io.github.opletter.koda

context(env: Environment)
private fun debugDeclarationShape(declaration: Declaration) {
    val value = when (declaration) {
        is Declaration.Def -> declaration.valueExpr
        is Declaration.Opaque -> declaration.valueExpr
        is Declaration.Thm -> declaration.valueExpr
        else -> return
    }
    val pending = ArrayDeque<Expression>()
    val seen = mutableSetOf<Int>()
    val forms = mutableMapOf<String, Int>()
    val constants = mutableMapOf<Name, Int>()
    pending.add(value)
    while (pending.isNotEmpty()) {
        val expression = pending.removeLast()
        if (!seen.add(expression.ie)) continue
        val form = expression::class.simpleName ?: "?"
        forms[form] = (forms[form] ?: 0) + 1
        when (expression) {
            is Expression.App -> {
                pending.add(expression.fnExpr)
                pending.add(expression.argExpr)
            }

            is Expression.Const -> constants[expression.name] = (constants[expression.name] ?: 0) + 1
            is Expression.ForallE -> {
                pending.add(expression.typeExpr)
                pending.add(expression.bodyExpr)
            }

            is Expression.Lam -> {
                pending.add(expression.typeExpr)
                pending.add(expression.bodyExpr)
            }

            is Expression.LetE -> {
                pending.add(expression.typeExpr)
                pending.add(expression.valueExpr)
                pending.add(expression.bodyExpr)
            }

            is Expression.Mdata -> pending.add(expression.expr)
            is Expression.Proj -> pending.add(expression.structExpr)
            is Expression.Bvar, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> {}
        }
    }
    fun Expression.shallow(depth: Int = 0): String {
        if (depth >= 4) return this::class.simpleName ?: "?"
        val [head, args] = asAppSpine()
        if (args.isNotEmpty()) {
            return "${head.shallow(depth + 1)}(${
                args.take(5).joinToString { it.shallow(depth + 1) }
            }${if (args.size > 5) ",..." else ""})"
        }
        return when (this) {
            is Expression.Const -> name.toStringDetailed()
            is Expression.NatVal -> natVal.toString()
            is Expression.Bvar -> "#$bvar"
            is Expression.Lam -> "lam(${bodyExpr.shallow(depth + 1)})"
            is Expression.LetE -> "let(${valueExpr.shallow(depth + 1)},${bodyExpr.shallow(depth + 1)})"
            is Expression.Mdata -> expr.shallow(depth + 1)
            is Expression.Proj -> "proj[$projIndex](${structExpr.shallow(depth + 1)})"
            is Expression.ForallE -> "forall(${bodyExpr.shallow(depth + 1)})"
            is Expression.Sort -> "sort"
            is Expression.StrVal -> "str"
            is Expression.App -> error("unreachable")
        }
    }
    println("debug declaration: ${declaration.name.toStringDetailed()} value=${value.shallow()}")
    println("debug nodes: total=${seen.size} forms=${forms.entries.sortedByDescending { it.value }}")
    println(
        "debug constants: " + constants.entries.sortedByDescending { it.value }.take(40)
            .joinToString { "${it.key.toStringDetailed()}=${it.value}" }
    )
}

context(env: Environment)
private fun Expression.debugContainsConstant(detailedName: String): Boolean {
    val pending = ArrayDeque<Expression>()
    val seen = mutableSetOf<Int>()
    pending.add(this)
    while (pending.isNotEmpty()) {
        val expression = pending.removeLast()
        if (!seen.add(expression.ie)) continue
        when (expression) {
            is Expression.App -> {
                pending.add(expression.fnExpr)
                pending.add(expression.argExpr)
            }

            is Expression.Const -> if (expression.name.toStringDetailed() == detailedName) return true
            is Expression.ForallE -> {
                pending.add(expression.typeExpr)
                pending.add(expression.bodyExpr)
            }

            is Expression.Lam -> {
                pending.add(expression.typeExpr)
                pending.add(expression.bodyExpr)
            }

            is Expression.LetE -> {
                pending.add(expression.typeExpr)
                pending.add(expression.valueExpr)
                pending.add(expression.bodyExpr)
            }

            is Expression.Mdata -> pending.add(expression.expr)
            is Expression.Proj -> pending.add(expression.structExpr)
            is Expression.Bvar, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> {}
        }
    }
    return false
}

context(env: Environment)
private fun Expression.debugHead(): String {
    val [head, args] = this.asAppSpine()
    val headName = (head as? Expression.Const)?.name?.toStringDetailed() ?: head::class.simpleName
    return "id=$ie head=$headName args=${args.size} loose=${maxLooseBVarIndex()}"
}

context(env: Environment)
private fun Expression.debugShallow(depth: Int = 0): String {
    if (depth >= 3) return debugHead()
    val [head, args] = asAppSpine()
    if (args.isNotEmpty()) {
        return "${head.debugShallow(depth + 1)}(${args.take(5).joinToString { it.debugShallow(depth + 1) }}" +
                if (args.size > 5) ",...)" else ")"
    }
    return when (this) {
        is Expression.Const -> name.toStringDetailed()
        is Expression.NatVal -> natVal.toString()
        is Expression.Bvar -> "#$bvar"
        is Expression.Lam -> "lam(${bodyExpr.debugShallow(depth + 1)})"
        is Expression.LetE -> "let(${valueExpr.debugShallow(depth + 1)},${bodyExpr.debugShallow(depth + 1)})"
        is Expression.Mdata -> expr.debugShallow(depth)
        is Expression.Proj -> "proj[$projIndex](${structExpr.debugShallow(depth + 1)})"
        is Expression.ForallE -> "forall(${bodyExpr.debugShallow(depth + 1)})"
        is Expression.Sort -> "sort"
        is Expression.StrVal -> "str"
        is Expression.App -> error("unreachable")
    }
}