package io.github.opletter.koda

import kotlin.time.TimeSource

data class DefEqCacheKey(
    val leftExprId: Int,
    val rightExprId: Int,
    val leftCtxId: Int,
    val rightCtxId: Int,
)

data class LocalCtxStepKey(
    val headExprId: Int,
    val tailCtxId: Int,
)

data class InferTypeCacheKey(
    val exprId: Int,
    val localCtxId: Int,
)

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
    val names: MutableMap<Int, Name> = mutableMapOf(0 to Name.Str(0, "", 0))
    val nameIndices: MutableMap<Name, Int> = mutableMapOf(Name.Str(0, "", 0) to 0)
    val declarations: MutableMap<Int, NamedDecl> = mutableMapOf()
    val levelParamByNameIndex: MutableMap<Int, Level.Param> = mutableMapOf()
    val constructorByName: MutableMap<Name, Inductive.ConstructorVal> = mutableMapOf()
    val rootInductiveByShortName: MutableMap<String, Pair<Int, Inductive.InductiveVal>> = mutableMapOf()
    val expressions: IntObjectStore<Expression> = IntObjectStore()
    val levels: IntObjectStore<Level> = IntObjectStore(listOf(0 to Level.Zero))

    val clock = TimeSource.Monotonic.markNow()

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()
    val reduceCacheNoLevelSubst: MutableMap<Int, Expression> = mutableMapOf()
    val liftCache: MutableMap<Long, Expression> = mutableMapOf()
    val applySubstSingleCache: MutableMap<Long, Expression> = mutableMapOf()
    val structureEtaInProgress: MutableSet<Long> = mutableSetOf()
    val defEqCache: MutableMap<DefEqCacheKey, Boolean> = mutableMapOf()
    val defEqInProgress: MutableSet<DefEqCacheKey> = mutableSetOf()
    val inferTypeCacheNoLevelSubst: MutableMap<InferTypeCacheKey, Expression> = mutableMapOf()
    val inferTypeInProgress: MutableSet<InferTypeCacheKey> = mutableSetOf()
    private val localCtxIntern: MutableMap<LocalCtxStepKey, Int> = mutableMapOf()
    private var nextLocalCtxId: Int = 1
    var defEqCalls: Long = 0
    var defEqCacheHits: Long = 0
    var defEqInProgressSkips: Long = 0
    var inferTypeCacheHits: Long = 0
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

    fun localCtxId(localCtx: List<Expression>): Int {
        if (localCtx.isEmpty()) return 0
        var ctxId = 0
        for (index in localCtx.indices.reversed()) {
            val stepKey = LocalCtxStepKey(localCtx[index].ie, ctxId)
            ctxId = localCtxIntern.getOrPut(stepKey) { nextLocalCtxId++ }
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
        reduceCacheNoLevelSubst.clear()
        liftCache.clear()
        applySubstSingleCache.clear()
        structureEtaInProgress.clear()
        defEqCache.clear()
        defEqInProgress.clear()
        inferTypeCacheNoLevelSubst.clear()
        inferTypeInProgress.clear()
        localCtxIntern.clear()
        nextLocalCtxId = 1
        defEqCalls = 0
        defEqCacheHits = 0
        defEqInProgressSkips = 0
        inferTypeCacheHits = 0
    }

    var shouldLog = false
    var shouldLog2 = false

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\n" +
                "Declarations:\n${declarations.toList().joinToString("\n")}\n\n" +
                "Expressions:\n${expressions.toList().joinToString("\n")}\n\n" +
                "Levels:\n${levels.toList().joinToString("\n")}"
    }
}