@file:OptIn(ExperimentalSerializationApi::class)

package io.github.opletter.koda

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.elementNames
import kotlinx.serialization.json.*
import kotlinx.serialization.serializer
import kotlin.jvm.JvmInline

// Use a custom discriminator since "type" (the default) is a field in some objects
private const val ExportTypeDiscriminator = "export_type"

@Serializable
@JvmInline
value class ExportTypeWrapper(val value: @Serializable(with = ExportType.Serializer::class) ExportType)

@Serializable
@JsonClassDiscriminator(ExportTypeDiscriminator)
sealed interface ExportType {
    object Serializer : JsonTransformingSerializer<ExportType>(serializer()) {
        val types = serializer<ExportType>().descriptor.getElementDescriptor(1).elementNames.toList()
        override fun transformDeserialize(element: JsonElement): JsonElement {
//            println("LOG (A): got $element, types: $types")
            element as? JsonObject ?: error("Expected JsonObject, got ${element::class.simpleName}")
            val keys = element.keys
            val type = keys.find { it in types } ?: error("Expected a key from types ($types), got $keys")
            val otherKey = (keys - type).firstOrNull()
            return when (val mainObj = element[type]!!) {
                is JsonObject -> JsonObject(mainObj + buildJsonObject {
                    if (otherKey != null) put(otherKey, element[otherKey]!!)
                    put(ExportTypeDiscriminator, type)
                })

                is JsonPrimitive, is JsonArray -> JsonObject(element + buildJsonObject {
                    put(ExportTypeDiscriminator, type)
                })
            }
        }
    }

    fun registerInto(env: Environment)
}

@Serializable
@SerialName("meta")
data class Meta(
    val exporter: Exporter,
    val lean: Lean,
    val format: Format,
) : ExportType {
    @Serializable
    data class Exporter(val name: String, val version: String)

    @Serializable
    data class Lean(val githash: String, val version: String)

    @Serializable
    data class Format(val version: String)

    override fun registerInto(env: Environment) {
        // no-op
    }
}

sealed class Name : ExportType {
    protected abstract val `in`: Int

    @Serializable
    @SerialName("str")
    data class Str(val pre: Int, val str: String, override val `in`: Int) : Name()

    @Serializable
    @SerialName("num")
    // TODO: `i` should be arbitrary precision
    data class Num(val pre: Int, val i: Long, override val `in`: Int) : Name()

    override fun registerInto(env: Environment) {
        env.names[this.`in`] = this
    }
}

sealed class Level : ExportType {
    protected abstract val il: Int // AKA "level index"

    data object Zero : Level() {
        override val il: Int
            get() = 0
    }

    @Serializable
    @SerialName("succ")
    data class Succ(private val succ: Int, override val il: Int) : Level() {
        context(env: Environment)
        val level get() = env.levels[succ] ?: error("Level $succ not found")
    }

    @Serializable
    @SerialName("max")
    data class Max(private val max: List<Int> /* size 2 */, override val il: Int) : Level() {
        context(env: Environment)
        val left get() = env.levels[max[0]] ?: error("Level ${max[0]} not found")

        context(env: Environment)
        val right get() = env.levels[max[1]] ?: error("Level ${max[1]} not found")
    }

    @Serializable
    @SerialName("imax")
    data class Imax(private val imax: List<Int> /* size 2 */, override val il: Int) : Level() {
        context(env: Environment)
        val left get() = env.levels[imax[0]] ?: error("Level ${imax[0]} not found")

        context(env: Environment)
        val right get() = env.levels[imax[1]] ?: error("Level ${imax[1]} not found")
    }

    @Serializable
    @SerialName("param")
    data class Param(private val param: Int, override val il: Int) : Level() {
        context(env: Environment)
        val name get() = env.names[param] ?: error("Name $param not found")
    }

    override fun registerInto(env: Environment) {
        // TODO: these checks are just for debugging
        check(il != 0) { "Level 0 is assumed" }
        check(il !in env.levels) { "Duplicate level $il" }
        env.levels[this.il] = this
    }

    context(env: Environment)
    fun toStringDetailed(): String = when (this) {
        is Zero -> "Zero"
        is Succ -> "Succ(level=${level.toStringDetailed()}, il=$il)"
        is Max -> "Max(left=${left.toStringDetailed()}, right=${right.toStringDetailed()}, il=$il)"
        is Imax -> "Imax(left=${left.toStringDetailed()}, right=${right.toStringDetailed()}, il=$il)"
        is Param -> "Param(name=$name, il=$il)"
    }
}

sealed class Expression : ExportType {
    protected abstract val ie: Int // AKA "expression index"

    @Serializable
    @SerialName("bvar")
    data class Bvar(val bvar: Int, override val ie: Int) : Expression()

    @Serializable
    @SerialName("sort")
    data class Sort(private val sort: Int, override val ie: Int) : Expression() {
        context(env: Environment)
        val level get() = env.levels[sort] ?: error("Level $sort not found")

        context(env: Environment)
        override fun toStringDetailed(): String {
            return "Sort(level=${level.toStringDetailed()}, ie=$ie)"
        }
    }

    @Serializable
    @SerialName("const")
    data class Const(@SerialName("name") private val _name: Int, private val us: List<Int>, override val ie: Int) :
        Expression() {
        context(env: Environment)
        val name get() = env.names[_name] ?: error("Name $_name not found")

        context(env: Environment)
        val decl get() = env.declarations[_name] ?: error("Declaration $name not found")

        context(env: Environment)
        val levels get() = us.map { env.levels[it] ?: error("Level $it not found") }
    }

    @Serializable
    @SerialName("app")
    data class App(private val fn: Int, private val arg: Int, override val ie: Int) :
        Expression() { // TODO: why are these documented as <number> and not <integer>
        context(env: Environment)
        val fnExpr get() = env.expressions[fn] ?: error("Expression $fn not found")

        context(env: Environment)
        val argExpr get() = env.expressions[arg] ?: error("Expression $arg not found")
    }

    @Serializable
    @SerialName("lam")
    data class Lam(
        @SerialName("name") private val _name: Int,
        private val type: Int,
        private val body: Int,
        val binderInfo: BinderInfo,
        override val ie: Int
    ) : Expression() {
        context(env: Environment)
        val name get() = env.names[_name] ?: error("Name $_name not found")

        context(env: Environment)
        val typeExpr get() = env.expressions[type] ?: error("Expression $type not found")

        context(env: Environment)
        val bodyExpr get() = env.expressions[body] ?: error("Expression $body not found")

        context(env: Environment)
        override fun toStringDetailed(): String {
            return "Lam(\n name=$name,\n type=${typeExpr.toStringDetailed().lines().joinToString("\n") { " $it"}},\n body=${bodyExpr.toStringDetailed().lines().joinToString("\n") { " $it"}},\n binderInfo=$binderInfo, ie=$ie)"
        }

        fun copyAsForAllE(): ForallE = ForallE(_name, type, body, binderInfo, ie)
    }

    @Serializable
    @SerialName("forallE")
    /** Also known as `pi` */
    data class ForallE(
        @SerialName("name") private val _name: Int,
        private val type: Int,
        private val body: Int,
        val binderInfo: BinderInfo,
        override val ie: Int
    ) : Expression() {
        context(env: Environment)
        val name get() = env.names[_name] ?: error("Name $_name not found")

        context(env: Environment)
        val typeExpr get() = env.expressions[type] ?: error("Expression $type not found")

        context(env: Environment)
        val bodyExpr get() = env.expressions[body] ?: error("Expression $body not found")

        context(env: Environment)
        override fun toStringDetailed(): String {
            return "ForallE(\n name=$name,\n type=${typeExpr.toStringDetailed().lines().joinToString("\n") { " $it"}},\n body=${bodyExpr.toStringDetailed().lines().joinToString("\n") { " $it"}}, binderInfo=$binderInfo, ie=$ie)"
        }
    }

    @Serializable
    @SerialName("letE")
    data class LetE(
        @SerialName("name") private val _name: Int,
        private val type: Int,
        private val value: Int,
        private val body: Int,
        val nondep: Boolean,
        override val ie: Int
    ) : Expression() {
        context(env: Environment)
        val name get() = env.names[_name] ?: error("Name $_name not found")

        context(env: Environment)
        val typeExpr get() = env.expressions[type] ?: error("Expression $type not found")

        context(env: Environment)
        val valueExpr get() = env.expressions[value] ?: error("Expression $value not found")

        context(env: Environment)
        val bodyExpr get() = env.expressions[body] ?: error("Expression $body not found")
    }

    @Serializable
    @SerialName("proj")
    data class Proj(
        private val typeName: Int,
        private val idx: Int,
        private val struct: Int,
        override val ie: Int
    ) : Expression() {
        // TODO: figure out what the indices represent
    }

    @Serializable
    @SerialName("natVal")
    data class NatVal(val natVal: Int, override val ie: Int) : Expression()

    @Serializable
    @SerialName("strVal")
    data class StrVal(val strVal: Int, override val ie: Int) : Expression()

    @Serializable
    @SerialName("mdata")
    data class Mdata(
        @SerialName("expr") private val _expr: Int,
        val data: JsonObject,
        override val ie: Int
    ) : Expression() {
        context(env: Environment)
        val expr get() = env.expressions[_expr] ?: error("Expression $_expr not found")
    }

    override fun registerInto(env: Environment) {
        env.expressions[this.ie] = this
    }

    context(env: Environment)
    open fun toStringDetailed(): String = this.toString() // why do I get an error without the `this`
}

sealed class Declaration : ExportType {
    // Not explicitly documented as part of every declaration, but they are present for all of them currently,
    // so for convenience, they are included in the interface.
    protected abstract val _name: Int
    protected abstract val _levelParams: List<Int>
    protected abstract val type: Int

    @Serializable
    @SerialName("axiom")
    data class Axiom(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        val isUnsafe: Boolean
    ) : Declaration()

    @Serializable
    @SerialName("def")
    data class Def(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        private val value: Int,
        // Can't put the serializer on `Hints` itself because it delegates to the default serializer
        @Serializable(with = HintsSerializer::class)
        val hints: Hints,
        val safety: Safety,
        private val all: List<Int>
    ) : Declaration() {
        context(env: Environment)
        val valueExpr get() = env.expressions[value] ?: error("Expression $value not found")

        context(env: Environment)
        val allNames get() = all.map { env.names[it] ?: error("Name $it not found") }

        enum class Safety {
            @SerialName("unsafe")
            Unsafe,

            @SerialName("safe")
            Safe,

            @SerialName("partial")
            Partial,
        }

        @Serializable
        sealed interface Hints {
            @Serializable
            @SerialName("opaque")
            data object Opaque : Hints

            @Serializable
            @SerialName("abbrev")
            data object Abbrev : Hints

            @Serializable
            @SerialName("regular")
            data class Regular(@SerialName("regular") val value: Int) : Hints

        }

        private object HintsSerializer : JsonTransformingSerializer<Hints>(serializer<Hints>()) {
            override fun transformDeserialize(element: JsonElement): JsonElement {
                return when (element) {
                    is JsonPrimitive -> buildJsonObject { put("type", element.content) }
                    is JsonObject -> JsonObject(element + ("type" to JsonPrimitive("regular")))
                    else -> error("Unknown Hints type: $element")
                }
            }
        }
    }

    @Serializable
    @SerialName("opaque")
    data class Opaque(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        private val value: Int,
        val isUnsafe: Boolean,
        private val all: List<Int>
    ) : Declaration() {
        context(env: Environment)
        val valueExpr get() = env.expressions[value] ?: error("Expression $value not found")

        context(env: Environment)
        val allNames get() = all.map { env.names[it] ?: error("Name $it not found") }
    }

    @Serializable
    @SerialName("thm")
    data class Thm(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        private val value: Int,
        private val all: List<Int>
    ) : Declaration() {
        context(env: Environment)
        val valueExpr get() = env.expressions[value] ?: error("Expression $value not found")

        context(env: Environment)
        val allNames get() = all.map { env.names[it] ?: error("Name $it not found") }
    }

    @Serializable
    @SerialName("quot")
    data class Quot(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        val kind: Kind,
    ) : Declaration() {
        enum class Kind {
            @SerialName("type")
            Type,

            @SerialName("ctor")
            Ctor,

            @SerialName("lift")
            Lift,

            @SerialName("ind")
            Ind,
        }
    }

    override fun registerInto(env: Environment) {
        val name = env.names[_name] ?: error("Name not found for $_name")
        name as? Name.Str ?: error("Expected Str name, got ${name::class.simpleName}")
        check(_name !in env.declarations) { "Duplicate declaration for ${name.str}" }
        env.declarations[this._name] = this
    }

    context(emv: Environment)
    val name get() = emv.names[this._name] ?: error("Name ${this._name} not found")

    context(emv: Environment)
    val levelParamsNames get() = this._levelParams.map { emv.names[it] ?: error("Level $it not found") }

    // this could probably be optimized
    context(emv: Environment)
    val levelParams get() = levelParamsNames.map { name ->
        emv.levels.entries.find { (it.value as? Level.Param)?.name == name }?.value ?: error("Level $name not found")
    }


    context(emv: Environment)
    val typeExpr get() = emv.expressions[this.type] ?: error("Expression ${this.type} not found")
}

// TODO: add context vals + make private
@Serializable
@SerialName("inductive")
data class Inductive(val types: List<InductiveVal>, val ctors: List<ConstructorVal>, val recs: List<RecursorVal>) :
    ExportType {
    @Serializable
    data class InductiveVal(
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val numParams: Int,
        val numIndices: Int,
        val all: List<Int>,
        val ctors: List<Int>,
        val numNested: Int,
        val isRec: Boolean,
        val isUnsafe: Boolean,
        val isReflexive: Boolean,
    )

    @Serializable
    data class ConstructorVal(
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val induct: Int,
        val cidx: Int,
        val numParams: Int,
        val numFields: Int,
        val isUnsafe: Boolean,
    )

    @Serializable
    data class RecursorVal(
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val all: List<Int>,
        val numParams: Int,
        val numIndices: Int,
        val numMotives: Int,
        val numMinors: Int,
        val rules: List<RecursorRule>,
        val k: Boolean,
        val isUnsafe: Boolean,
    ) {
        @Serializable
        data class RecursorRule(val ctor: Int, val nfields: Int, val rhs: Int)
    }

    override fun registerInto(env: Environment) {
        TODO()
    }
}

enum class BinderInfo {
    @SerialName("default")
    Default,

    @SerialName("implicit")
    Implicit,

    @SerialName("strictImplicit")
    StrictImplicit,

    @SerialName("instImplicit")
    InstImplicit,
}