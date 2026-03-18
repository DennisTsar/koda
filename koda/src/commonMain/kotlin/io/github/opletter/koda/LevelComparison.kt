package io.github.opletter.koda

context(env: Environment)
fun Level.isEqual(other: Level): Boolean = this.isLessOrEqual(other) && other.isLessOrEqual(this)

// Based on the reference implementation in Type Checking in Lean 4, which is from Gabriel Ebner's Lean 3 checker trepplein
// https://ammkrn.github.io/type_checking_in_lean4/levels.html#partial-order-on-levels
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
private inline fun <T> withTemporaryLevel(levelIndex: Int, tempLevel: Level, block: () -> T): T {
    val previousLevel = env.levels[levelIndex] ?: error("Level $levelIndex not found")
    env.levels[levelIndex] = tempLevel
    return try {
        block()
    } finally {
        env.levels[levelIndex] = previousLevel
    }
}

context(env: Environment)
private fun compareByCases(paramLevel: Level.Param, compare: () -> Boolean): Boolean {
    val caseZero = withTemporaryLevel(paramLevel.il, Level.Zero) { compare() }
    val tempParamLevel = env.addCustomLevel { paramLevel.copy(il = it) }
    val succLevel = Level.Succ(tempParamLevel, paramLevel.il)
    val caseSucc = withTemporaryLevel(paramLevel.il, succLevel) { compare() }
    return caseZero && caseSucc
}

context(env: Environment)
private fun Level.simplify(): Level = when (this) {
    is Level.Imax if this.right.isEqual(Level.Zero) -> Level.Zero
    is Level.Imax if this.right is Level.Succ -> {
        val maxLevel = env.addCustomLevel {
            Level.Max(listOf(this.left.il, this.right.il), it)
        }
        env.levels[maxLevel]!!
    }

    else -> this
}