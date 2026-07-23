package io.github.opletter.koda

import kotlin.time.TimeSource

data class DefEqCacheKey(
    val leftExprId: Int,
    val rightExprId: Int,
    val leftCtxId: Int,
    val rightCtxId: Int,
)

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
    private val nonNegative: MutableList<T?> = mutableListOf()
    private val negative: MutableMap<Int, T> = mutableMapOf()

    init {
        initialEntries.forEach { pair -> this[pair.first] = pair.second }
    }

    private fun ensureNonNegativeSize(size: Int) {
        if (nonNegative.size >= size) return
        repeat(size - nonNegative.size) { nonNegative.add(null) }
    }

    operator fun get(index: Int): T? {
        return if (index >= 0) {
            nonNegative.getOrNull(index)
        } else {
            negative[index]
        }
    }

    operator fun get(index: Int?): T? = index?.let { this[it] }

    operator fun set(index: Int, value: T) {
        if (index >= 0) {
            ensureNonNegativeSize(index + 1)
            nonNegative[index] = value
        } else {
            negative[index] = value
        }
    }

    operator fun contains(index: Int): Boolean {
        return this[index] != null
    }

    fun clearNegative() {
        negative.clear()
    }

    val values: Sequence<T>
        get() = sequence {
            nonNegative.forEach { value -> if (value != null) yield(value) }
            negative.values.forEach { value -> yield(value) }
        }

    fun toList(): List<Pair<Int, T>> {
        val items = mutableListOf<Pair<Int, T>>()
        nonNegative.forEachIndexed { index, value ->
            if (value != null) items += index to value
        }
        negative.entries.sortedBy { it.key }.forEach { entry ->
            items += entry.toPair()
        }
        return items
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

    val clock = TimeSource.Monotonic.markNow()

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()
    val whnfCacheNoLevelSubst: MutableMap<Int, Expression> = mutableMapOf()
    val whnfCacheWithCtxNoLevelSubst: MutableMap<ReduceCacheKey, Expression> = mutableMapOf()
    val natLiteralCacheNoLevelSubst: MutableMap<ReduceCacheKey, NatValue?> = mutableMapOf()
    val liftCache: MutableMap<ExprPairKey, Expression> = mutableMapOf()
    val applySubstSingleCache: MutableMap<ExprPairKey, Expression> = mutableMapOf()
    val unfoldedDefinitionCache: MutableMap<Int, Expression> = mutableMapOf()
    val maxLooseBVarIndexCache: IntObjectStore<Int> = IntObjectStore()
    val projectionReductionInfoByNameIndex: MutableMap<Int, ProjectionReductionInfo?> = mutableMapOf()
    internal val natLiteralRecursorRulesCache: MutableMap<Name, NatLiteralRecursorRules?> = mutableMapOf()
    val defEqCache: MutableMap<DefEqCacheKey, Boolean> = mutableMapOf()
    val defEqAppFailures: MutableSet<DefEqCacheKey> = mutableSetOf()
    val inferTypeCacheNoLevelSubst: MutableMap<InferTypeCacheKey, Expression> = mutableMapOf()
    private val localCtxIntern: MutableMap<LocalCtxStepKey, Int> = mutableMapOf()
    private var nextLocalCtxId: Int = 1
    var defEqCalls: Long = 0
    var defEqCacheHits: Long = 0
    var inferTypeCacheHits: Long = 0
    var proofIrrelevanceAttempts: Long = 0
    var proofIrrelevanceSuccesses: Long = 0
    var typedCongruenceProofSkips: Long = 0
    var eagerReduction = false
    private val customLevelIntern: MutableMap<LevelKey, Level> = mutableMapOf()
    private val customExprIntern: MutableMap<ExprKey, Expression> = mutableMapOf()
    private var nextLevelIndex: Int = 0

    private sealed interface LevelKey {
        data class Succ(val levelIl: Int) : LevelKey
        data class Max(val leftIl: Int, val rightIl: Int) : LevelKey
        data class Imax(val leftIl: Int, val rightIl: Int) : LevelKey
        data class Param(val name: Name) : LevelKey
    }

    private sealed interface ExprKey {
        data class Bvar(val bvar: Int) : ExprKey
        data class Sort(val levelIl: Int) : ExprKey
        data class Const(val name: Name, val levelIls: List<Int>) : ExprKey
        data class App(val fnIe: Int, val argIe: Int) : ExprKey
        data class ForallE(val name: Name, val typeIe: Int, val bodyIe: Int, val binderInfo: BinderInfo) : ExprKey
        data class Lam(val name: Name, val typeIe: Int, val bodyIe: Int, val binderInfo: BinderInfo) : ExprKey
        data class LetE(
            val name: Name,
            val typeIe: Int,
            val valueIe: Int,
            val bodyIe: Int,
            val nonDep: Boolean,
        ) : ExprKey

        data class Mdata(val data: Any, val exprIe: Int) : ExprKey
        data class Proj(val typeName: Name, val idx: Int, val structIe: Int) : ExprKey
        data class NatVal(val natVal: NatValue) : ExprKey
        data class StrVal(val strVal: String) : ExprKey
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

    private fun Expression.toExprKey(): ExprKey? = when (this) {
        is Expression.Bvar -> ExprKey.Bvar(this.bvar)
        is Expression.Sort -> ExprKey.Sort(this.level.il)
        is Expression.Const -> ExprKey.Const(this.name, this.levels.map { it.il })
        is Expression.App -> ExprKey.App(this.fnExpr.ie, this.argExpr.ie)
        is Expression.ForallE -> ExprKey.ForallE(this.name, this.typeExpr.ie, this.bodyExpr.ie, this.binderInfo)
        is Expression.Lam -> ExprKey.Lam(this.name, this.typeExpr.ie, this.bodyExpr.ie, this.binderInfo)
        is Expression.LetE -> ExprKey.LetE(
            this.name,
            this.typeExpr.ie,
            this.valueExpr.ie,
            this.bodyExpr.ie,
            this.nondep
        )

        is Expression.Mdata -> ExprKey.Mdata(this.data, this.expr.ie)
        is Expression.Proj -> ExprKey.Proj(this.typeNameExpr, this.projIndex, this.structExpr.ie)
        is Expression.NatVal -> ExprKey.NatVal(this.natVal)
        is Expression.StrVal -> ExprKey.StrVal(this.strVal)
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

    fun addCustomExpr(exprConstructor: (Int) -> Expression): Expression {
        val candidateIndex = nextExprIndex - 1
        val newExpr = exprConstructor(candidateIndex) // MEM: 3.71 GB
        val internKey = newExpr.toExprKey()
        if (internKey != null) {
            customExprIntern[internKey]?.let { return it }
        }
        nextExprIndex = candidateIndex
        expressions[nextExprIndex] = newExpr // MEM: 5.68 GB
        if (internKey != null) {
            customExprIntern[internKey] = newExpr
        }
        return newExpr
    }

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
        levels.clearNegative() // MEM: 100 MB
        nextLevelIndex = 0
        customLevelIntern.clear()
        expressions.clearNegative() // MEM: 924 MB
        nextExprIndex = -100
        customExprIntern.clear()
        whnfCacheNoLevelSubst.clear()
        whnfCacheWithCtxNoLevelSubst.clear()
        natLiteralCacheNoLevelSubst.clear()
        liftCache.clear()
        applySubstSingleCache.clear()
        unfoldedDefinitionCache.clear()
        maxLooseBVarIndexCache.clearNegative()
        defEqCache.clear()
        defEqAppFailures.clear()
        inferTypeCacheNoLevelSubst.clear()
        localCtxIntern.clear()
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
