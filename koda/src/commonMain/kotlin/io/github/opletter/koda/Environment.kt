package io.github.opletter.koda

import kotlin.time.TimeSource

data class DefEqCacheKey(
    val leftExprId: Int,
    val rightExprId: Int,
    val leftCtxId: Int,
    val rightCtxId: Int,
)

class DefEqEquivalenceManager {
    private var keys = LongArray(16)
    private var nodeRefs = IntArray(16)
    private var parents = IntArray(16)
    private var ranks = ByteArray(16)
    private var nodeCount = 0
    private var entryCount = 0

    fun areEquivalent(key: DefEqCacheKey): Boolean {
        val leftNode = findNode(contextualKey(key.leftExprId, key.leftCtxId))
        if (leftNode < 0) return false
        val rightNode = findNode(contextualKey(key.rightExprId, key.rightCtxId))
        return rightNode >= 0 && findRoot(leftNode) == findRoot(rightNode)
    }

    fun addEquivalent(key: DefEqCacheKey) {
        val leftNode = getOrCreateNode(contextualKey(key.leftExprId, key.leftCtxId))
        val rightNode = getOrCreateNode(contextualKey(key.rightExprId, key.rightCtxId))
        union(leftNode, rightNode)
    }

    private fun contextualKey(exprId: Int, ctxId: Int): Long =
        (exprId.toLong() shl 32) xor (ctxId.toLong() and 0xffffffffL)

    private fun startIndex(key: Long): Int {
        var hash = key
        hash = hash xor (hash ushr 33)
        hash *= -49064778989728563L
        hash = hash xor (hash ushr 33)
        return hash.toInt() and (keys.size - 1)
    }

    private fun findNode(key: Long): Int {
        var index = startIndex(key)
        while (true) {
            val nodeRef = nodeRefs[index]
            if (nodeRef == 0) return -1
            if (keys[index] == key) return nodeRef - 1
            index = (index + 1) and (keys.size - 1)
        }
    }

    private fun getOrCreateNode(key: Long): Int {
        if ((entryCount + 1) * 10 >= keys.size * 7) resizeTable()
        var index = startIndex(key)
        while (true) {
            val nodeRef = nodeRefs[index]
            if (nodeRef == 0) {
                val node = createNode()
                keys[index] = key
                nodeRefs[index] = node + 1
                entryCount++
                return node
            }
            if (keys[index] == key) return nodeRef - 1
            index = (index + 1) and (keys.size - 1)
        }
    }

    private fun createNode(): Int {
        if (nodeCount == parents.size) {
            parents = parents.copyOf(nodeCount * 2)
            ranks = ranks.copyOf(nodeCount * 2)
        }
        val node = nodeCount++
        parents[node] = node
        return node
    }

    private fun findRoot(node: Int): Int {
        var root = node
        while (parents[root] != root) root = parents[root]
        var current = node
        while (parents[current] != current) {
            val next = parents[current]
            parents[current] = root
            current = next
        }
        return root
    }

    private fun union(leftNode: Int, rightNode: Int) {
        val leftRoot = findRoot(leftNode)
        val rightRoot = findRoot(rightNode)
        if (leftRoot == rightRoot) return
        when {
            ranks[leftRoot] < ranks[rightRoot] -> parents[leftRoot] = rightRoot
            ranks[leftRoot] > ranks[rightRoot] -> parents[rightRoot] = leftRoot
            else -> {
                parents[rightRoot] = leftRoot
                ranks[leftRoot] = (ranks[leftRoot] + 1).toByte()
            }
        }
    }

    private fun resizeTable() {
        val oldKeys = keys
        val oldNodeRefs = nodeRefs
        keys = LongArray(oldKeys.size * 2)
        nodeRefs = IntArray(oldNodeRefs.size * 2)
        oldNodeRefs.forEachIndexed { oldIndex, nodeRef ->
            if (nodeRef == 0) return@forEachIndexed
            val key = oldKeys[oldIndex]
            var index = startIndex(key)
            while (nodeRefs[index] != 0) index = (index + 1) and (keys.size - 1)
            keys[index] = key
            nodeRefs[index] = nodeRef
        }
    }
}

data class LocalCtxStepKey(
    val headTypeExprId: Int,
    val headValueExprId: Int?,
    val tailCtxId: Int,
)

private class LocalContext(
    val head: Expression,
    val headValue: Expression?,
    val tail: List<Expression>,
    val internId: Int,
) : AbstractList<Expression>() {
    override val size: Int = tail.size + 1

    override fun get(index: Int): Expression {
        if (index !in indices) throw IndexOutOfBoundsException("Index $index out of bounds for context of size $size")
        var remaining = index
        var current: List<Expression> = this
        while (current is LocalContext) {
            if (remaining == 0) return current.head
            remaining -= 1
            current = current.tail
        }
        return current[remaining]
    }

    fun valueAt(index: Int): Expression? {
        if (index !in indices) throw IndexOutOfBoundsException("Index $index out of bounds for context of size $size")
        var remaining = index
        var current: List<Expression> = this
        while (current is LocalContext) {
            if (remaining == 0) return current.headValue
            remaining -= 1
            current = current.tail
        }
        return null
    }
}

data class InferTypeCacheKey(
    val exprId: Int,
    val localCtxId: Int,
    val validate: Boolean,
)

data class ReduceCacheKey(
    val exprId: Int,
    val localCtxId: Int,
)

data class ExprPairKey(val firstExprId: Int, val second: Int)

internal fun exprPairKey(first: Int, second: Int): Long =
    (first.toLong() shl 32) xor (second.toLong() and 0xffffffffL)

internal class LongObjectStore<T> {
    private var keys = LongArray(16)
    private var values: Array<Any?> = arrayOfNulls(16)
    var size = 0
        private set

    private fun startIndex(key: Long): Int {
        val folded = (key xor (key ushr 32)).toInt()
        return (folded xor (folded ushr 16)) and (keys.size - 1)
    }

    operator fun get(key: Long): T? {
        var index = startIndex(key)
        while (true) {
            @Suppress("UNCHECKED_CAST")
            val value = values[index] as T? ?: return null
            if (keys[index] == key) return value
            index = (index + 1) and (keys.size - 1)
        }
    }

    operator fun set(key: Long, value: T) {
        if ((size + 1) * 3 >= keys.size * 2) resize()
        insert(key, value)
    }

    private fun insert(key: Long, value: T) {
        var index = startIndex(key)
        while (true) {
            if (values[index] == null) {
                keys[index] = key
                values[index] = value
                size++
                return
            }
            if (keys[index] == key) {
                values[index] = value
                return
            }
            index = (index + 1) and (keys.size - 1)
        }
    }

    private fun resize() {
        val oldKeys = keys
        val oldValues = values
        keys = LongArray(oldKeys.size * 2)
        values = arrayOfNulls(oldValues.size * 2)
        size = 0
        oldValues.forEachIndexed { index, value ->
            @Suppress("UNCHECKED_CAST")
            if (value != null) insert(oldKeys[index], value as T)
        }
    }
}

data class ProjectionReductionInfo(
    val inductiveNameIndex: Int,
    val fieldIndex: Int,
    val arity: Int,
    val structArgIndex: Int,
)

class NameIndexStore {
    private var keys: Array<Name?> = arrayOfNulls(16)
    private var values: IntArray = IntArray(16)
    private var size = 0

    private fun startIndex(key: Name): Int = key.hashCode() and (keys.size - 1)

    operator fun get(key: Name): Int? {
        var index = startIndex(key)
        while (true) {
            val current = keys[index] ?: return null
            if (current == key) return values[index]
            index = (index + 1) and (keys.size - 1)
        }
    }

    operator fun set(key: Name, value: Int) {
        if ((size + 1) * 3 >= keys.size * 2) resize()
        insert(key, value)
    }

    private fun insert(key: Name, value: Int) {
        var index = startIndex(key)
        while (true) {
            val current = keys[index]
            if (current == null) {
                keys[index] = key
                values[index] = value
                size += 1
                return
            }
            if (current == key) {
                values[index] = value
                return
            }
            index = (index + 1) and (keys.size - 1)
        }
    }

    private fun resize() {
        val oldKeys = keys
        val oldValues = values
        keys = arrayOfNulls(oldKeys.size * 2)
        values = IntArray(keys.size)
        size = 0
        oldKeys.forEachIndexed { index, key ->
            if (key != null) insert(key, oldValues[index])
        }
    }
}

class IntObjectStore<T>(initialEntries: List<Pair<Int, T>> = emptyList()) {
    private var sourceEntries: Array<Any?> = arrayOfNulls(16)
    private var sourceSize = 0
    private var syntheticEntries: Array<Any?> = arrayOfNulls(16)
    private var syntheticSize = 0

    init {
        initialEntries.forEach { pair -> this[pair.first] = pair.second }
    }

    private fun grow(entries: Array<Any?>, size: Int): Array<Any?> =
        if (entries.size >= size) entries else entries.copyOf(maxOf(size, entries.size + entries.size / 2))

    private fun syntheticPosition(index: Int): Int = -index - 1

    operator fun get(index: Int): T? {
        @Suppress("UNCHECKED_CAST")
        return if (index >= 0) {
            if (index < sourceSize) sourceEntries[index] as T? else null
        } else {
            val position = syntheticPosition(index)
            if (position < syntheticSize) syntheticEntries[position] as T? else null
        }
    }

    operator fun get(index: Int?): T? = index?.let { this[it] }

    operator fun set(index: Int, value: T) {
        if (index >= 0) {
            sourceEntries = grow(sourceEntries, index + 1)
            sourceEntries[index] = value
            if (index >= sourceSize) sourceSize = index + 1
        } else {
            val position = syntheticPosition(index)
            syntheticEntries = grow(syntheticEntries, position + 1)
            syntheticEntries[position] = value
            if (position >= syntheticSize) syntheticSize = position + 1
        }
    }

    operator fun contains(index: Int): Boolean {
        return this[index] != null
    }

    fun clearSynthetic() {
        syntheticEntries = arrayOfNulls(16)
        syntheticSize = 0
    }

    val values: Sequence<T>
        get() = sequence {
            for (index in 0 until sourceSize) {
                @Suppress("UNCHECKED_CAST")
                val value = sourceEntries[index] as T?
                if (value != null) yield(value)
            }
            for (position in 0 until syntheticSize) {
                @Suppress("UNCHECKED_CAST")
                val value = syntheticEntries[position] as T?
                if (value != null) yield(value)
            }
        }

    fun toList(): List<Pair<Int, T>> {
        val items = mutableListOf<Pair<Int, T>>()
        for (index in 0 until sourceSize) {
            @Suppress("UNCHECKED_CAST")
            val value = sourceEntries[index] as T?
            if (value != null) items += index to value
        }
        for (position in syntheticSize - 1 downTo 0) {
            @Suppress("UNCHECKED_CAST")
            val value = syntheticEntries[position] as T? ?: continue
            items += -(position + 1) to value
        }
        return items
    }
}

private class ExpressionMetadataStore {
    private var source = IntArray(16)
    private var synthetic = IntArray(16)

    private fun position(index: Int): Int = if (index >= 0) index else -index - 1

    private fun grow(entries: IntArray, size: Int): IntArray =
        if (entries.size >= size) entries else entries.copyOf(maxOf(size, entries.size + entries.size / 2))

    private fun packed(index: Int): Int {
        val position = position(index)
        val entries = if (index >= 0) source else synthetic
        return if (position < entries.size) entries[position] else 0
    }

    fun setMaxLooseBVarIndex(index: Int, maxLooseBVarIndex: Int) {
        val position = position(index)
        if (index >= 0) {
            source = grow(source, position + 1)
            source[position] = ((maxLooseBVarIndex + 1) shl 2) or (source[position] and 3)
        } else {
            synthetic = grow(synthetic, position + 1)
            synthetic[position] = ((maxLooseBVarIndex + 1) shl 2) or (synthetic[position] and 3)
        }
    }

    fun incrementReferenceCount(index: Int) {
        val position = position(index)
        if (index >= 0) {
            source = grow(source, position + 1)
            if ((source[position] and 3) < 2) source[position]++
        } else {
            synthetic = grow(synthetic, position + 1)
            if ((synthetic[position] and 3) < 2) synthetic[position]++
        }
    }

    fun maxLooseBVarIndex(index: Int): Int = (packed(index) ushr 2) - 1
    fun isShared(index: Int): Boolean = (packed(index) and 3) >= 2

    fun clearSynthetic() {
        synthetic = IntArray(16)
    }
}

class Environment {
    val names: IntObjectStore<Name> = IntObjectStore(listOf(0 to Name.Str(0, "", 0)))
    val nameIndices: NameIndexStore = NameIndexStore().also { it[Name.Str(0, "", 0)] = 0 }
    val declarations: IntObjectStore<NamedDecl> = IntObjectStore()
    val levelParamByNameIndex: MutableMap<Int, Level.Param> = mutableMapOf()
    val constructorByName: MutableMap<Name, Inductive.ConstructorVal> = mutableMapOf()
    val rootInductiveByShortName: MutableMap<String, Pair<Int, Inductive.InductiveVal>> = mutableMapOf()
    val expressions: IntObjectStore<Expression> = IntObjectStore()
    val levels: IntObjectStore<Level> = IntObjectStore(listOf(0 to Level.Zero))
    var levelNormalizationCache: MutableMap<Int, Level> = mutableMapOf()

    val clock = TimeSource.Monotonic.markNow()

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()
    var whnfCacheNoLevelSubst: MutableMap<Int, Expression> = mutableMapOf()
    var whnfCacheWithCtxNoLevelSubst: MutableMap<ReduceCacheKey, Expression> = mutableMapOf()
    var natLiteralCacheNoLevelSubst: MutableMap<ReduceCacheKey, NatValue?> = mutableMapOf()
    internal var liftCache = LongObjectStore<Expression>()
    internal var applySubstSingleCache = LongObjectStore<Expression>()
    var unfoldedDefinitionCache: MutableMap<Int, Expression> = mutableMapOf()
    val projectionReductionInfoByNameIndex: MutableMap<Int, ProjectionReductionInfo?> = mutableMapOf()
    internal val natLiteralRecursorRulesCache: MutableMap<Name, NatLiteralRecursorRules?> = mutableMapOf()
    internal val structureEtaRecursorCache: MutableMap<Name, StructureEtaRecursorInfo?> = mutableMapOf()
    var defEqCache: MutableSet<DefEqCacheKey> = mutableSetOf()
    var defEqAppFailures: MutableSet<DefEqCacheKey> = mutableSetOf()
    var defEqEquivalences = DefEqEquivalenceManager()
    var inferTypeCacheNoLevelSubst: MutableMap<InferTypeCacheKey, Expression> = mutableMapOf()
    private var localCtxIntern: MutableMap<LocalCtxStepKey, Int> = mutableMapOf()
    private var nextLocalCtxId: Int = 1
    var defEqCalls: Long = 0
    var defEqCacheHits: Long = 0
    var inferTypeCacheHits: Long = 0
    var proofIrrelevanceAttempts: Long = 0
    var proofIrrelevanceSuccesses: Long = 0
    var typedCongruenceProofSkips: Long = 0
    var eagerReduction = false
    private var customLevelIntern: MutableMap<LevelKey, Level> = mutableMapOf()
    private var customExprIntern = ExpressionInterner()
    private var nextLevelIndex: Int = 0
    private val expressionMetadata = ExpressionMetadataStore()

    private sealed interface LevelKey {
        data class Succ(val levelIl: Int) : LevelKey
        data class Max(val leftIl: Int, val rightIl: Int) : LevelKey
        data class Imax(val leftIl: Int, val rightIl: Int) : LevelKey
        data class Param(val name: Name) : LevelKey
    }

    private fun Level.toLevelKey(): LevelKey = with(this@Environment) {
        when (this@toLevelKey) {
            Level.Zero -> error("Zero should not be interned as custom level")
            is Level.Succ -> LevelKey.Succ(this@toLevelKey.level.il)
            is Level.Max -> LevelKey.Max(this@toLevelKey.left.il, this@toLevelKey.right.il)
            is Level.Imax -> LevelKey.Imax(this@toLevelKey.left.il, this@toLevelKey.right.il)
            is Level.Param -> LevelKey.Param(this@toLevelKey.name)
        }
    }

    private inner class ExpressionInterner {
        private var hashes = IntArray(16)
        private var expressions = arrayOfNulls<Expression>(16)
        private var size = 0

        fun intern(candidate: Expression): Expression {
            val hash = structuralHash(candidate)
            var slot = findSlot(candidate, hash)
            expressions[slot]?.let { return it }

            if ((size + 1) * 10 >= expressions.size * 7) {
                resize()
                slot = findSlot(candidate, hash)
            }
            hashes[slot] = hash
            expressions[slot] = candidate
            size++
            return candidate
        }

        private fun findSlot(candidate: Expression, hash: Int): Int {
            val mask = expressions.lastIndex
            var slot = spreadHash(hash) and mask
            while (true) {
                val existing = expressions[slot] ?: return slot
                if (hashes[slot] == hash && structurallyEqual(candidate, existing)) return slot
                slot = (slot + 1) and mask
            }
        }

        private fun resize() {
            val oldHashes = hashes
            val oldExpressions = expressions
            hashes = IntArray(oldHashes.size * 2)
            expressions = arrayOfNulls(oldExpressions.size * 2)
            val mask = expressions.lastIndex
            oldExpressions.forEachIndexed { index, expression ->
                if (expression == null) return@forEachIndexed
                val hash = oldHashes[index]
                var slot = spreadHash(hash) and mask
                while (expressions[slot] != null) slot = (slot + 1) and mask
                hashes[slot] = hash
                expressions[slot] = expression
            }
        }

        private fun spreadHash(hash: Int): Int = hash xor (hash ushr 16)

        private fun mix(hash: Int, value: Int): Int = hash * 31 + value

        private fun structuralHash(expr: Expression): Int {
            // Expression index is the final data-class field, so subtracting it leaves a hash of the serialized node.
            val nodeHash = expr.hashCode() - expr.ie
            val kind = when (expr) {
                is Expression.Bvar -> 1
                is Expression.Sort -> 2
                is Expression.Const -> 3
                is Expression.App -> 4
                is Expression.ForallE -> 5
                is Expression.Lam -> 6
                is Expression.LetE -> 7
                is Expression.Mdata -> 8
                is Expression.Proj -> 9
                is Expression.NatVal -> 10
                is Expression.StrVal -> 11
            }
            return mix(kind, nodeHash)
        }

        private fun structurallyEqual(left: Expression, right: Expression): Boolean {
            return when (left) {
                is Expression.Bvar -> right is Expression.Bvar && left.copy(ie = right.ie) == right
                is Expression.Sort -> right is Expression.Sort && left.copy(ie = right.ie) == right
                is Expression.Const -> right is Expression.Const && left.copy(ie = right.ie) == right
                is Expression.App -> right is Expression.App && left.copy(ie = right.ie) == right
                is Expression.ForallE -> right is Expression.ForallE && left.copy(ie = right.ie) == right
                is Expression.Lam -> right is Expression.Lam && left.copy(ie = right.ie) == right
                is Expression.LetE -> right is Expression.LetE && left.copy(ie = right.ie) == right
                is Expression.Mdata -> right is Expression.Mdata && left.copy(ie = right.ie) == right
                is Expression.Proj -> right is Expression.Proj && left.copy(ie = right.ie) == right
                is Expression.NatVal -> right is Expression.NatVal && left.copy(ie = right.ie) == right
                is Expression.StrVal -> right is Expression.StrVal && left.copy(ie = right.ie) == right
            }
        }
    }

    fun addCustomLevel(levelConstructor: (Int) -> Level): Level {
        val candidateIndex = nextLevelIndex - 1
        val newLevel = levelConstructor(candidateIndex)
        val internKey = newLevel.toLevelKey()
        customLevelIntern[internKey]?.let { return it }

        nextLevelIndex = candidateIndex
        levels[nextLevelIndex] = newLevel
        customLevelIntern[internKey] = newLevel
        return newLevel
    }

    fun addCustomSuccLevel(levelIl: Int): Level {
        val key = LevelKey.Succ(levelIl)
        customLevelIntern[key]?.let { return it }
        val candidateIndex = nextLevelIndex - 1
        val newLevel = Level.Succ(levelIl, candidateIndex)
        nextLevelIndex = candidateIndex
        levels[nextLevelIndex] = newLevel
        customLevelIntern[key] = newLevel
        return newLevel
    }

    fun addCustomMaxLevel(leftIl: Int, rightIl: Int): Level {
        val key = LevelKey.Max(leftIl, rightIl)
        customLevelIntern[key]?.let { return it }
        val candidateIndex = nextLevelIndex - 1
        val newLevel = Level.Max(listOf(leftIl, rightIl), candidateIndex)
        nextLevelIndex = candidateIndex
        levels[nextLevelIndex] = newLevel
        customLevelIntern[key] = newLevel
        return newLevel
    }

    fun addCustomImaxLevel(leftIl: Int, rightIl: Int): Level {
        val key = LevelKey.Imax(leftIl, rightIl)
        customLevelIntern[key]?.let { return it }
        val candidateIndex = nextLevelIndex - 1
        val newLevel = Level.Imax(listOf(leftIl, rightIl), candidateIndex)
        nextLevelIndex = candidateIndex
        levels[nextLevelIndex] = newLevel
        customLevelIntern[key] = newLevel
        return newLevel
    }

    fun addCustomParamLevel(nameIndex: Int): Level {
        val name = names[nameIndex] ?: error("Name $nameIndex not found")
        val key = LevelKey.Param(name)
        customLevelIntern[key]?.let { return it }
        val candidateIndex = nextLevelIndex - 1
        val newLevel = Level.Param(nameIndex, candidateIndex)
        nextLevelIndex = candidateIndex
        levels[nextLevelIndex] = newLevel
        customLevelIntern[key] = newLevel
        return newLevel
    }

    private var nextExprIndex: Int = -100 // Could start with 0, but this helps while debugging vs levels

    internal fun registerSourceExpression(expression: Expression) {
        expressions[expression.ie] = expression
        recordExpressionMetadata(expression)
    }

    fun addCustomExpr(exprConstructor: (Int) -> Expression): Expression {
        val candidateIndex = nextExprIndex - 1
        val newExpr = exprConstructor(candidateIndex)
        val internedExpr = customExprIntern.intern(newExpr)
        if (internedExpr !== newExpr) return internedExpr
        nextExprIndex = candidateIndex
        expressions[nextExprIndex] = newExpr
        recordExpressionMetadata(newExpr)
        return newExpr
    }

    private fun recordExpressionMetadata(expression: Expression) {
        fun recordChild(childId: Int): Int {
            expressionMetadata.incrementReferenceCount(childId)
            return expressionMetadata.maxLooseBVarIndex(childId)
        }

        fun Int.descendBinder(): Int = if (this < 0) -1 else this - 1

        val maxLooseBVarIndex = when (expression) {
            is Expression.Bvar -> expression.bvar
            is Expression.App -> maxOf(recordChild(expression.fn), recordChild(expression.arg))
            is Expression.ForallE -> maxOf(
                recordChild(expression.type),
                recordChild(expression.body).descendBinder(),
            )

            is Expression.Lam -> maxOf(
                recordChild(expression.type),
                recordChild(expression.body).descendBinder(),
            )

            is Expression.LetE -> maxOf(
                recordChild(expression.type),
                recordChild(expression.value),
                recordChild(expression.body).descendBinder(),
            )

            is Expression.Mdata -> recordChild(expression._expr)
            is Expression.Proj -> recordChild(expression.struct)
            is Expression.Const, is Expression.NatVal, is Expression.Sort, is Expression.StrVal -> -1
        }
        expressionMetadata.setMaxLooseBVarIndex(expression.ie, maxLooseBVarIndex)
    }

    fun expressionMaxLooseBVarIndex(exprId: Int): Int = expressionMetadata.maxLooseBVarIndex(exprId)
    fun expressionIsShared(exprId: Int): Boolean = expressionMetadata.isShared(exprId)

    private fun localCtxStepId(headTypeExprId: Int, headValueExprId: Int?, tailCtxId: Int): Int {
        val stepKey = LocalCtxStepKey(headTypeExprId, headValueExprId, tailCtxId)
        return localCtxIntern.getOrPut(stepKey) { nextLocalCtxId++ }
    }

    fun consLocalCtx(
        head: Expression,
        tail: List<Expression>,
        value: Expression? = null,
    ): List<Expression> {
        return LocalContext(head, value, tail, localCtxStepId(head.ie, value?.ie, localCtxId(tail)))
    }

    fun localCtxValue(localCtx: List<Expression>, index: Int): Expression? {
        return (localCtx as? LocalContext)?.valueAt(index)
    }

    fun localCtxId(localCtx: List<Expression>): Int {
        if (localCtx.isEmpty()) return 0
        if (localCtx is LocalContext) return localCtx.internId
        var ctxId = 0
        for (index in localCtx.indices.reversed()) {
            ctxId = localCtxStepId(localCtx[index].ie, null, ctxId)
        }
        return ctxId
    }

    fun clearCustom() {
        levels.clearSynthetic()
        nextLevelIndex = 0
        customLevelIntern = mutableMapOf()
        levelNormalizationCache = mutableMapOf()
        expressions.clearSynthetic()
        nextExprIndex = -100
        customExprIntern = ExpressionInterner()
        expressionMetadata.clearSynthetic()
        whnfCacheNoLevelSubst = mutableMapOf()
        whnfCacheWithCtxNoLevelSubst = mutableMapOf()
        natLiteralCacheNoLevelSubst = mutableMapOf()
        liftCache = LongObjectStore()
        applySubstSingleCache = LongObjectStore()
        unfoldedDefinitionCache = mutableMapOf()
        defEqCache = mutableSetOf()
        defEqAppFailures = mutableSetOf()
        defEqEquivalences = DefEqEquivalenceManager()
        inferTypeCacheNoLevelSubst = mutableMapOf()
        localCtxIntern = mutableMapOf()
        nextLocalCtxId = 1
        defEqCalls = 0
        defEqCacheHits = 0
        inferTypeCacheHits = 0
        proofIrrelevanceAttempts = 0
        proofIrrelevanceSuccesses = 0
        typedCongruenceProofSkips = 0
        eagerReduction = false
    }

    var shouldLog = false

    var counter = 0

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\n" +
                "Declarations:\n${declarations.toList().joinToString("\n")}\n\n" +
                "Expressions:\n${expressions.toList().joinToString("\n")}\n\n" +
                "Levels:\n${levels.toList().joinToString("\n")}"
    }
}
