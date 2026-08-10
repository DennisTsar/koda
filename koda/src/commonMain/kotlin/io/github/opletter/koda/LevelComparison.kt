package io.github.opletter.koda

private data class LevelOffset(val base: Level, val offset: Int)

private data class LevelComparisonKey(val greater: Int, val lesser: Int)

context(env: Environment)
fun Level.isEqual(other: Level): Boolean {
    if (this === other || this.il == other.il) return true
    val forward = this.trySimpleIsLessOrEqual(other)
    if (forward == false) return false
    val backward = other.trySimpleIsLessOrEqual(this)
    if (backward == false) return false
    if (forward == true && backward == true) return true
    return this.normalizeLevel().il == other.normalizeLevel().il
}

context(env: Environment)
fun List<Level>.isEqual(other: List<Level>): Boolean =
    size == other.size && (this == other || indices.all { this[it].isEqual(other[it]) })

context(env: Environment)
fun makeLevelMax(left: Level, right: Level): Level {
    val leftOffset = left.toOffset()
    val rightOffset = right.toOffset()
    if (leftOffset.base === Level.Zero && rightOffset.base === Level.Zero) {
        return if (leftOffset.offset >= rightOffset.offset) left else right
    }
    if (left.il == right.il) return left
    if (left === Level.Zero) return right
    if (right === Level.Zero) return left
    if (right is Level.Max && (right.left.il == left.il || right.right.il == left.il)) return right
    if (left is Level.Max && (left.left.il == right.il || left.right.il == right.il)) return left

    if (leftOffset.base.il == rightOffset.base.il) {
        return if (leftOffset.offset >= rightOffset.offset) left else right
    }
    return env.addCustomMaxLevel(left.il, right.il)
}

context(env: Environment)
fun makeLevelImax(left: Level, right: Level): Level {
    if (right.isDefinitelyNonzero()) return makeLevelMax(left, right)
    if (right === Level.Zero) return Level.Zero
    if (left === Level.Zero || left.toOffset().let { it.base === Level.Zero && it.offset == 1 }) return right
    if (left.il == right.il) return left
    return env.addCustomImaxLevel(left.il, right.il)
}

context(env: Environment)
fun Level.isLessOrEqual(other: Level): Boolean {
    this.trySimpleIsLessOrEqual(other)?.let { return it }
    val lesser = this.normalizeLevel()
    val greater = other.normalizeLevel()
    val cache = mutableMapOf<LevelComparisonKey, Boolean>()

    fun isGeq(left: Level, right: Level): Boolean {
        val key = LevelComparisonKey(left.il, right.il)
        cache[key]?.let { return it }

        val result = when {
            left.il == right.il || right === Level.Zero -> true
            right is Level.Max -> isGeq(left, right.left) && isGeq(left, right.right)
            left is Level.Max && (isGeq(left.left, right) || isGeq(left.right, right)) -> true
            right is Level.Imax -> isGeq(left, right.left) && isGeq(left, right.right)
            left is Level.Imax -> isGeq(left.right, right)
            else -> {
                val leftOffset = left.toOffset()
                val rightOffset = right.toOffset()
                when {
                    leftOffset.base.il == rightOffset.base.il || rightOffset.base === Level.Zero ->
                        leftOffset.offset >= rightOffset.offset

                    leftOffset.offset == rightOffset.offset && leftOffset.offset > 0 ->
                        isGeq(leftOffset.base, rightOffset.base)

                    else -> false
                }
            }
        }
        cache[key] = result
        return result
    }

    return isGeq(greater, lesser)
}

context(env: Environment)
private fun Level.trySimpleIsLessOrEqual(other: Level, balance: Int = 0): Boolean? = when {
    balance == 0 && other === Level.Zero -> this.isDefinitelyLeZero()
    this.il == other.il && balance >= 0 -> true
    this === Level.Zero && balance >= 0 -> true
    other === Level.Zero && balance < 0 -> false
    this is Level.Param && other is Level.Param -> this.name == other.name && balance >= 0
    this is Level.Param && other === Level.Zero -> false
    this === Level.Zero && other is Level.Param -> balance >= 0
    this is Level.Succ -> this.level.trySimpleIsLessOrEqual(other, balance - 1)
    other is Level.Succ -> this.trySimpleIsLessOrEqual(other.level, balance + 1)
    this is Level.Max -> {
        val leftResult = this.left.trySimpleIsLessOrEqual(other, balance)
        if (leftResult == false) {
            false
        } else {
            val rightResult = this.right.trySimpleIsLessOrEqual(other, balance)
            when {
                rightResult == false -> false
                leftResult == true && rightResult == true -> true
                else -> null
            }
        }
    }

    (this is Level.Param || this === Level.Zero) && other is Level.Max -> {
        val leftResult = this.trySimpleIsLessOrEqual(other.left, balance)
        if (leftResult == true) {
            true
        } else {
            val rightResult = this.trySimpleIsLessOrEqual(other.right, balance)
            when {
                rightResult == true -> true
                leftResult == false && rightResult == false -> false
                else -> null
            }
        }
    }

    else -> null
}

context(env: Environment)
private fun Level.isDefinitelyLeZero(): Boolean = when (this) {
    Level.Zero -> true
    is Level.Param, is Level.Succ -> false
    is Level.Max -> this.left.isDefinitelyLeZero() && this.right.isDefinitelyLeZero()
    is Level.Imax -> this.right.isDefinitelyLeZero()
}

context(env: Environment)
private fun Level.normalizeLevel(): Level {
    env.levelNormalizationCache[this.il]?.let { return it }

    val offset = this.toOffset()
    val normalized = when (val base = offset.base) {
        Level.Zero -> Level.Zero.addOffset(offset.offset)
        is Level.Param -> env.addCustomParamLevel(base.nameIndex).addOffset(offset.offset)
        is Level.Imax ->
            makeLevelImax(
                base.left.normalizeLevel(),
                base.right.normalizeLevel(),
            ).addOffset(offset.offset)

        is Level.Max -> {
            val rawArgs = mutableListOf<Level>()
            base.forEachMaxArgument { rawArgs += it }

            val normalizedArgs = mutableListOf<Level>()
            rawArgs.forEach { argument ->
                argument.normalizeLevel().forEachMaxArgument {
                    normalizedArgs += it.addOffset(offset.offset)
                }
            }
            makeNormalizedMax(normalizedArgs)
        }

        is Level.Succ -> error("toOffset returned a successor base")
    }

    env.levelNormalizationCache[this.il] = normalized
    return normalized
}

context(env: Environment)
private inline fun Level.forEachMaxArgument(action: (Level) -> Unit) {
    val pending = ArrayDeque<Level>()
    pending.addLast(this)
    while (pending.isNotEmpty()) {
        when (val current = pending.removeLast()) {
            is Level.Max -> {
                pending.addLast(current.right)
                pending.addLast(current.left)
            }

            else -> action(current)
        }
    }
}

context(env: Environment)
private fun Level.toOffset(): LevelOffset {
    var base = this
    var offset = 0
    while (base is Level.Succ) {
        base = base.level
        offset += 1
    }
    return LevelOffset(base, offset)
}

context(env: Environment)
private fun Level.addOffset(amount: Int): Level {
    var result = this
    repeat(amount) {
        result = env.addCustomSuccLevel(result.il)
    }
    return result
}

context(env: Environment)
private fun makeNormalizedMax(arguments: List<Level>): Level {
    check(arguments.isNotEmpty())

    val greatestByBase = mutableMapOf<Int, LevelOffset>()
    val pending = ArrayDeque<Level>()
    arguments.asReversed().forEach(pending::addLast)
    while (pending.isNotEmpty()) {
        when (val argument = pending.removeLast()) {
            is Level.Max -> {
                pending.addLast(argument.right)
                pending.addLast(argument.left)
            }

            else -> {
                val offset = argument.toOffset()
                val previous = greatestByBase[offset.base.il]
                if (previous == null || previous.offset < offset.offset) {
                    greatestByBase[offset.base.il] = offset
                }
            }
        }
    }

    val explicit = greatestByBase[Level.Zero.il]
    if (
        explicit != null &&
        greatestByBase.values.any { it.base !== Level.Zero && it.offset >= explicit.offset }
    ) {
        greatestByBase.remove(Level.Zero.il)
    }

    val reduced = greatestByBase.values
        .sortedWith(compareBy<LevelOffset>({ it.base.il }, { it.offset }))
        .map { it.base.addOffset(it.offset) }
    if (reduced.size == 1) return reduced.single()

    var result = reduced.last()
    for (index in reduced.lastIndex - 1 downTo 0) {
        result = env.addCustomMaxLevel(reduced[index].il, result.il)
    }
    return result
}

context(env: Environment)
private fun Level.isDefinitelyNonzero(): Boolean = when (this) {
    Level.Zero, is Level.Param -> false
    is Level.Succ -> true
    is Level.Max -> this.left.isDefinitelyNonzero() || this.right.isDefinitelyNonzero()
    is Level.Imax -> this.right.isDefinitelyNonzero()
}
