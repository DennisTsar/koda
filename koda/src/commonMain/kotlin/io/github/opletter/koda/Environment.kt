package io.github.opletter.koda

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
    val declarations: MutableMap<Int, NamedDecl> = mutableMapOf()
    val expressions: IntObjectStore<Expression> = IntObjectStore()
    val levels: IntObjectStore<Level> = IntObjectStore(listOf(0 to Level.Zero))

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()
    val reduceCacheNoLevelSubst: MutableMap<Int, Expression> = mutableMapOf()
    val liftCache: MutableMap<Long, Expression> = mutableMapOf()
    val applySubstSingleCache: MutableMap<Long, Expression> = mutableMapOf()
    val structureEtaInProgress: MutableSet<Long> = mutableSetOf()
    private val customExprIntern: MutableMap<ExprKey, Expression> = mutableMapOf()
    private var nextLevelIndex: Int = 0

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
        is Expression.NatVal, is Expression.StrVal -> null
    }

    fun addCustomLevel(levelConstructor: (Int) -> Level): Level {
        nextLevelIndex--
        val newLevel = levelConstructor(nextLevelIndex)
        levels[nextLevelIndex] = newLevel
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

    fun clearCustom() {
        levels.clearNegative() // MEM: 100 MB
        nextLevelIndex = 0
        expressions.clearNegative() // MEM: 924 MB
        nextExprIndex = -100
        customExprIntern.clear()
        reduceCacheNoLevelSubst.clear()
        liftCache.clear()
        applySubstSingleCache.clear()
        structureEtaInProgress.clear()
    }

    var shouldLog = false

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\n" +
                "Declarations:\n${declarations.toList().joinToString("\n")}\n\n" +
                "Expressions:\n${expressions.toList().joinToString("\n")}\n\n" +
                "Levels:\n${levels.toList().joinToString("\n")}"
    }
}