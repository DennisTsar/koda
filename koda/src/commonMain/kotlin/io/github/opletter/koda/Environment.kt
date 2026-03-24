package io.github.opletter.koda

class Environment {
    val names: MutableMap<Int, Name> = mutableMapOf(0 to Name.Str(0, "", 0))
    val declarations: MutableMap<Int, NamedDecl> = mutableMapOf()
    val expressions: MutableMap<Int, Expression> = mutableMapOf()
    val levels: MutableMap<Int, Level> = mutableMapOf(0 to Level.Zero)

    val declTypeByName: MutableMap<Name, Expression> = mutableMapOf()
    val reduceCacheNoLevelSubst: MutableMap<Int, Expression> = mutableMapOf()

    private var nextLevelIndex: Int = 0

    fun addCustomLevel(levelConstructor: (Int) -> Level): Level {
        nextLevelIndex--
        val newLevel = levelConstructor(nextLevelIndex)
        levels[nextLevelIndex] = newLevel
        return newLevel
    }

    private var nextExprIndex: Int = -100 // Could start with 0, but this helps while debugging vs levels

    fun addCustomExpr(exprConstructor: (Int) -> Expression): Expression {
        nextExprIndex--
        val newExpr = exprConstructor(nextExprIndex) // MEM: 3.71 GB
        expressions[nextExprIndex] = newExpr // MEM: 5.68 GB
        return newExpr
    }

    fun clearCustom() {
        (nextLevelIndex..-1).forEach { levels.remove(it) } // MEM: 100 MB
        nextLevelIndex = 0
        (nextExprIndex..-101).forEach { expressions.remove(it) } // MEM: 924 MB
        nextExprIndex = -100
        reduceCacheNoLevelSubst.clear()
    }

    var shouldLog = false

    override fun toString(): String {
        return "Names:\n${names.toList().joinToString("\n")}\n\n" +
                "Declarations:\n${declarations.toList().joinToString("\n")}\n\n" +
                "Expressions:\n${expressions.toList().joinToString("\n")}\n\n" +
                "Levels:\n${levels.toList().joinToString("\n")}"
    }
}
