package io.github.opletter.koda

private enum class NatPrimitiveKind(val arity: Int) {
    Succ(1),
    Add(2),
    Sub(2),
    Mul(2),
    Pow(2),
    Div(2),
    Mod(2),
    Beq(2),
    Ble(2),
}

private data class NatSuccChainForReduction(
    val count: Long,
    val base: Expression,
)

context(env: Environment)
fun Expression.App.tryReduceNatPrimitive(levelSubst: Map<Int, Level>): Expression? {
    val [headExpr, args] = this.unfoldApp()
    val headConst = headExpr as? Expression.Const ?: return null
    val primitiveKind = headConst.tryGetNatPrimitiveKind() ?: return null
    if (args.size != primitiveKind.arity) return null

    fun makeNatLiteral(value: NatValue): Expression {
        return env.addCustomExpr { Expression.NatVal(value, it) }
    }

    fun reduceOperand(index: Int): NatValue? {
        return args[index].tryEvalNatLiteral(levelSubst)
    }

    val reduced: Expression? = when (primitiveKind) {
        NatPrimitiveKind.Succ -> {
            val input = reduceOperand(0) ?: return null
            makeNatLiteral(input + NatValue.ONE)
        }

        NatPrimitiveKind.Add -> {
            val left = reduceOperand(0) ?: return null
            val right = reduceOperand(1) ?: return null
            makeNatLiteral(left + right)
        }

        NatPrimitiveKind.Sub -> {
            val left = reduceOperand(0) ?: return null
            val right = reduceOperand(1) ?: return null
            makeNatLiteral(left.saturatingMinus(right))
        }

        NatPrimitiveKind.Mul -> {
            val left = reduceOperand(0) ?: return null
            val right = reduceOperand(1) ?: return null
            makeNatLiteral(left * right)
        }

        NatPrimitiveKind.Pow -> {
            val base = reduceOperand(0) ?: return null
            val exponent = reduceOperand(1) ?: return null
            makeNatLiteral(base.pow(exponent))
        }

        NatPrimitiveKind.Div -> {
            val dividend = reduceOperand(0) ?: return null
            val divisor = reduceOperand(1) ?: return null
            makeNatLiteral(dividend.div(divisor))
        }

        NatPrimitiveKind.Mod -> {
            val dividend = reduceOperand(0) ?: return null
            val divisor = reduceOperand(1) ?: return null
            makeNatLiteral(dividend.mod(divisor))
        }

        NatPrimitiveKind.Beq -> {
            val left = reduceOperand(0) ?: return null
            val right = reduceOperand(1) ?: return null
            makeBoolCtor(left == right)
        }

        NatPrimitiveKind.Ble -> {
            val left = reduceOperand(0) ?: return null
            val right = reduceOperand(1) ?: return null
            makeBoolCtor(left <= right)
        }
    }

    if (reduced != null && env.shouldLog) {
        println("nat-reduced ${primitiveKind.name} ${this.toStringDetailed()} -> ${reduced.toStringDetailed()}")
    }
    return reduced
}

context(env: Environment)
private fun Expression.Const.tryGetNatPrimitiveKind(): NatPrimitiveKind? {
    if (this.levels.isNotEmpty()) return null

    val fullName = this.name
    val leafName = fullName as? Name.Str ?: return null
    val namespace = env.names[leafName.pre] as? Name.Str ?: return null
    if (namespace.pre != 0 || namespace.str != "Nat") return null

    return when (leafName.str) {
        "succ" -> NatPrimitiveKind.Succ
        "add" -> NatPrimitiveKind.Add
        "sub" -> NatPrimitiveKind.Sub
        "mul" -> NatPrimitiveKind.Mul
        "pow" -> NatPrimitiveKind.Pow
        "div" -> NatPrimitiveKind.Div
        "mod" -> NatPrimitiveKind.Mod
        "beq" -> NatPrimitiveKind.Beq
        "ble" -> NatPrimitiveKind.Ble
        else -> null
    }
}

context(env: Environment)
private fun Expression.tryAsNatLiteralForReduction(): NatValue? {
    return when (this) {
        is Expression.NatVal -> this.natVal
        is Expression.Const -> if (this.isNatZeroCtorForReduction()) NatValue.ZERO else null
        is Expression.App -> {
            val chain = this.tryUnfoldNatSuccChainForReduction() ?: return null
            val baseLiteral = chain.base.tryAsNatLiteralForReduction() ?: return null
            baseLiteral + NatValue.fromString(chain.count.toString())
        }

        else -> null
    }
}

context(env: Environment)
private fun Expression.tryEvalNatLiteral(levelSubst: Map<Int, Level>, depth: Int = 0): NatValue? {
    if (depth > 256) return null
    val expr = this.instantiateLevelParams(levelSubst)
    expr.tryAsNatLiteralForReduction()?.let { return it }

    val app = expr as? Expression.App ?: return null
    val [headExpr, args] = app.unfoldApp()
    val headConst = headExpr as? Expression.Const ?: return null
    val primitiveKind = headConst.tryGetNatPrimitiveKind() ?: return null
    if (args.size != primitiveKind.arity) return null

    fun evalArg(index: Int): NatValue? = args[index].tryEvalNatLiteral(levelSubst, depth + 1)

    return when (primitiveKind) {
        NatPrimitiveKind.Succ -> evalArg(0)?.plus(NatValue.ONE)
        NatPrimitiveKind.Add -> {
            val left = evalArg(0) ?: return null
            val right = evalArg(1) ?: return null
            left + right
        }

        NatPrimitiveKind.Sub -> {
            val left = evalArg(0) ?: return null
            val right = evalArg(1) ?: return null
            left.saturatingMinus(right)
        }

        NatPrimitiveKind.Mul -> {
            val left = evalArg(0) ?: return null
            val right = evalArg(1) ?: return null
            left * right
        }

        NatPrimitiveKind.Pow -> {
            val base = evalArg(0) ?: return null
            val exponent = evalArg(1) ?: return null
            base.pow(exponent)
        }

        NatPrimitiveKind.Div -> {
            val dividend = evalArg(0) ?: return null
            val divisor = evalArg(1) ?: return null
            dividend.div(divisor)
        }

        NatPrimitiveKind.Mod -> {
            val dividend = evalArg(0) ?: return null
            val divisor = evalArg(1) ?: return null
            dividend.mod(divisor)
        }

        NatPrimitiveKind.Beq,
        NatPrimitiveKind.Ble -> null
    }
}

context(env: Environment)
private fun Expression.tryUnfoldNatSuccChainForReduction(): NatSuccChainForReduction? {
    var current: Expression = this
    var succCount = 0L

    while (true) {
        val app = current as? Expression.App ?: break
        if (!app.fnExpr.isNatSuccCtorForReduction()) break
        if (succCount == Long.MAX_VALUE) return null
        succCount += 1
        current = app.argExpr
    }

    return if (succCount == 0L) null else NatSuccChainForReduction(succCount, current)
}

context(env: Environment)
private fun Expression.isNatSuccCtorForReduction(): Boolean {
    return this.isNatCtorForReduction(expectedNumFields = 1)
}

context(env: Environment)
private fun Expression.isNatZeroCtorForReduction(): Boolean {
    return this.isNatCtorForReduction(expectedNumFields = 0)
}

context(env: Environment)
private fun Expression.isNatCtorForReduction(expectedNumFields: Int): Boolean {
    val constExpr = this as? Expression.Const ?: return false
    val ctorDecl = constExpr.decl as? Inductive.ConstructorVal ?: return false
    if (ctorDecl.numParams != 0 || ctorDecl.numFields != expectedNumFields) return false
    val inductiveName = ctorDecl.inductName as? Name.Str ?: return false
    return inductiveName.pre == 0 && inductiveName.str == "Nat"
}

context(env: Environment)
private fun makeBoolCtor(value: Boolean): Expression? {
    val boolEntry = env.rootInductiveByShortName["Bool"] ?: return null
    val boolNameIndex = boolEntry.first
    val boolDecl = boolEntry.second
    val targetName = if (value) "true" else "false"
    val targetCidx = if (value) 1 else 0

    val ctorIndex = boolDecl.ctors.firstOrNull { index: Int ->
        val ctorDecl = env.declarations[index] as? Inductive.ConstructorVal ?: return@firstOrNull false
        if (ctorDecl.numParams != 0 || ctorDecl.numFields != 0) return@firstOrNull false
        val ctorName = ctorDecl.name as? Name.Str ?: return@firstOrNull false
        ctorName.pre == boolNameIndex && ctorName.str == targetName
    } ?: boolDecl.ctors.firstOrNull { index: Int ->
        val ctorDecl = env.declarations[index] as? Inductive.ConstructorVal ?: return@firstOrNull false
        ctorDecl.numParams == 0 && ctorDecl.numFields == 0 && ctorDecl.cidx == targetCidx
    } ?: return null

    return env.addCustomExpr {
        Expression.Const(_name = ctorIndex, us = emptyList(), ie = it)
    }
}