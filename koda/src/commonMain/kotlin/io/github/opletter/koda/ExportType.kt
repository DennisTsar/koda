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
        env.nameIndices[this] = this.`in`
    }
}

context(env: Environment)
tailrec fun Name.toStringDetailed(suffix: String? = null): String {
    //    return buildString {
//    }
    fun String?.prependIfNotNull(): String? = if (this != null) ".$this" else ""
    return when (this) {
        is Name.Num -> env.names[this.pre.takeIf { it != 0 }]?.toStringDetailed("${this.i}${suffix.prependIfNotNull()}")
            ?: "${this.i}.${suffix.orEmpty()}"

        is Name.Str -> env.names[this.pre.takeIf { it != 0 }]?.toStringDetailed("${this.str}${suffix.prependIfNotNull()}")
            ?: "${this.str}.${suffix.orEmpty()}"
    }
}

sealed class Level : ExportType {
    abstract val il: Int // AKA "level index"

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
        val nameIndex get() = param

        context(env: Environment)
        val name get() = env.names[param] ?: error("Name $param not found")
    }

    override fun registerInto(env: Environment) {
        // TODO: these checks are just for debugging
        check(il != 0) { "Level 0 is assumed" }
        check(il !in env.levels) { "Duplicate level $il" }
        env.levels[this.il] = this
        if (this is Param) {
            env.levelParamByNameIndex[this.nameIndex] = this
        }
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
    abstract val ie: Int // AKA "expression index"
    internal var looseBVarRange: Int = -1

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

        context(env: Environment)
        override fun toStringDetailed(): String {
            return "App(\n fn=${
                fnExpr.toStringDetailed().lines().joinToString("\n") { " $it" }
            },\n arg=${argExpr.toStringDetailed().lines().joinToString("\n") { " $it" }},\n ie=$ie)"
        }
    }

    @Serializable
    @SerialName("lam")
    data class Lam(
        @SerialName("name") private val _name: Int,
        private val type: Int,
        private val body: Int,
        val binderInfo: BinderInfo,
        override val ie: Int,
    ) : Expression() {
        context(env: Environment)
        val name get() = env.names[_name] ?: error("Name $_name not found")

        context(env: Environment)
        val typeExpr get() = env.expressions[type] ?: error("Expression $type not found")

        context(env: Environment)
        val bodyExpr get() = env.expressions[body] ?: error("Expression $body not found")

        context(env: Environment)
        override fun toStringDetailed(): String {
            return "Lam(\n name=$name,\n type=${
                typeExpr.toStringDetailed().lines().joinToString("\n") { " $it" }
            },\n body=${
                bodyExpr.toStringDetailed().lines().joinToString("\n") { " $it" }
            },\n binderInfo=$binderInfo, ie=$ie)"
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
        override val ie: Int,
    ) : Expression() {
        context(env: Environment)
        val name get() = env.names[_name] ?: error("Name $_name not found")

        context(env: Environment)
        val typeExpr get() = env.expressions[type] ?: error("Expression $type not found")

        context(env: Environment)
        val bodyExpr get() = env.expressions[body] ?: error("Expression $body not found")

        context(env: Environment)
        override fun toStringDetailed(): String {
            return "ForallE(\n name=$name,\n type=${
                typeExpr.toStringDetailed().lines().joinToString("\n") { " $it" }
            },\n body=${
                bodyExpr.toStringDetailed().lines().joinToString("\n") { " $it" }
            }, binderInfo=$binderInfo, ie=$ie)"
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
        override val ie: Int,
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
        override val ie: Int,
    ) : Expression() {
        context(env: Environment)
        val typeNameExpr get() = env.names[typeName] ?: error("Name $typeName not found")

        context(env: Environment)
        val typeDecl get() = env.declarations[typeName] ?: error("Declaration for $typeNameExpr not found")

        val projIndex get() = idx

        context(env: Environment)
        val structExpr get() = env.expressions[struct] ?: error("Expression $struct not found")

        val typeNameIndex get() = typeName
    }

    @Serializable
    @SerialName("natVal")
    data class NatVal(val natVal: NatValue, override val ie: Int) : Expression()

    @Serializable
    @SerialName("strVal")
    data class StrVal(val strVal: String, override val ie: Int) : Expression()

    @Serializable
    @SerialName("mdata")
    data class Mdata(
        @SerialName("expr") private val _expr: Int,
        val data: JsonObject,
        override val ie: Int,
    ) : Expression() {
        context(env: Environment)
        val expr get() = env.expressions[_expr] ?: error("Expression $_expr not found")
    }

    override fun registerInto(env: Environment) {
        env.expressions[this.ie] = this
        env.initializeLooseBVarRange(this)
    }

    context(env: Environment)
    open fun toStringDetailed(): String = this.toString() // why do I get an error without the `this`
}

sealed class Declaration : ExportType, NamedDecl() {
    @Serializable
    @SerialName("axiom")
    data class Axiom(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        val isUnsafe: Boolean,
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
        private val all: List<Int>,
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
        private val all: List<Int>,
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
        private val all: List<Int>,
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
        check(_name !in env.declarations) { "Duplicate declaration for $name" }
        env.declarations[this._name] = this
    }
}

// TODO: add context vals + make private
@Serializable
@SerialName("inductive")
data class Inductive(
    val types: List<InductiveVal>,
    val ctors: List<ConstructorVal>,
    val recs: List<RecursorVal>,
) : ExportType {
    val type get() = types.singleOrNull() ?: error("Inductive with more than one type not supported. found: $types")

    @Serializable
    data class InductiveVal(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        val numParams: Int,
        val numIndices: Int,
        val all: List<Int>,
        val ctors: List<Int>,
        val numNested: Int,
        val isRec: Boolean,
        val isUnsafe: Boolean,
        val isReflexive: Boolean,
    ) : NamedDecl() {
        fun registerInto(env: Environment) {
            val name = env.names[_name] ?: error("Name not found for $_name")
            check(_name !in env.declarations) { "Duplicate declaration for $name" }
            env.declarations[this._name] = this
            val strName = name as? Name.Str
            if (strName != null && strName.pre == 0) {
                env.rootInductiveByShortName[strName.str] = this._name to this
            }
        }
    }

    @Serializable
    data class ConstructorVal(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        private val induct: Int,
        val cidx: Int,
        val numParams: Int,
        val numFields: Int,
        val isUnsafe: Boolean,
    ) : NamedDecl() {
        context(env: Environment)
        val inductName get() = env.names[induct] ?: error("Name $induct not found")

        fun registerInto(env: Environment) {
            val name = env.names[_name] ?: error("Name not found for $_name")
            check(_name !in env.declarations) { "Duplicate declaration for $name" }
            env.declarations[this._name] = this
            env.constructorByName[name] = this
        }
    }

    @Serializable
    data class RecursorVal(
        @SerialName("name") override val _name: Int,
        @SerialName("levelParams") override val _levelParams: List<Int>,
        override val type: Int,
        val all: List<Int>,
        val numParams: Int,
        val numIndices: Int,
        val numMotives: Int,
        val numMinors: Int,
        val rules: List<RecursorRule>,
        val k: Boolean,
        val isUnsafe: Boolean,
    ) : NamedDecl() {
        @Serializable
        data class RecursorRule(private val ctor: Int, val nfields: Int, private val rhs: Int) {
            context(env: Environment)
            val ctorName get() = env.names[ctor] ?: error("Name $ctor not found")

            context(env: Environment)
            val rhsExpr get() = env.expressions[rhs] ?: error("Expression $rhs not found")
        }

        fun registerInto(env: Environment) {
            val name = env.names[_name] ?: error("Name not found for $_name")
            check(_name !in env.declarations) { "Duplicate declaration for $name" }
            env.declarations[this._name] = this
        }
    }

    override fun registerInto(env: Environment) {
        types.forEach { it.registerInto(env) }
        ctors.forEach { it.registerInto(env) }
        recs.forEach { it.registerInto(env) }
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


sealed class NamedDecl {
    // Not explicitly documented as part of every declaration, but they are present for all of them currently,
    // so for convenience, they are included in the interface.
    protected abstract val _name: Int
    protected abstract val _levelParams: List<Int>
    protected abstract val type: Int

    val levelParamIndices get() = this._levelParams

    context(env: Environment)
    val name get() = env.names[this._name] ?: error("Name ${this._name} not found")

    context(env: Environment)
    val levelParamsNames get() = this._levelParams.map { env.names[it] ?: error("Level $it not found") }

    // O(1) lookup via environment-side mapping populated during level registration.
    context(env: Environment)
    val levelParams
        get() = this._levelParams.map { levelParamNameIndex ->
            env.levelParamByNameIndex[levelParamNameIndex]
                ?: error("Level param index $levelParamNameIndex not found")
        }

    context(env: Environment)
    val typeExpr get() = env.expressions[this.type] ?: error("Expression ${this.type} not found")
}
