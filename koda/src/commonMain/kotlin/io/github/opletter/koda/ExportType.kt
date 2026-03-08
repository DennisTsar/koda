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
}

sealed interface Name : ExportType {
    @SerialName("in") // can't use "in" as variable name without backticks
    val in2: Int

    @Serializable
    @SerialName("str")
    data class Str(val pre: Int, val str: String, @SerialName("in") override val in2: Int) : Name

    @Serializable
    @SerialName("num")
    data class Num(val pre: Int, val i: Long, @SerialName("in") override val in2: Int) : Name
}

sealed interface Level : ExportType {
    val il: Int

    @Serializable
    @SerialName("succ")
    data class Succ(val succ: Int, override val il: Int) : Level

    @Serializable
    @SerialName("max")
    data class Max(val max: List<Int> /* size 2 */, override val il: Int) : Level

    @Serializable
    @SerialName("imax")
    data class Imax(val imax: List<Int> /* size 2 */, override val il: Int) : Level

    @Serializable
    @SerialName("param")
    data class Param(val param: Int, override val il: Int) : Level
}

@Serializable
sealed interface Expression : ExportType {
    val ie: Int

    @Serializable
    @SerialName("bvar")
    data class Bvar(val bvar: Int, override val ie: Int) : Expression

    @Serializable
    @SerialName("sort")
    data class Sort(val sort: Int, override val ie: Int) : Expression

    @Serializable
    @SerialName("const")
    data class Const(val name: Int, val us: List<Int>, override val ie: Int) : Expression

    @Serializable
    @SerialName("app")
    data class App(val fn: Double, val arg: Double, override val ie: Int) : Expression

    @Serializable
    @SerialName("lam")
    data class Lam(val name: Int, val type: Int, val body: Int, val binderInfo: BinderInfo, override val ie: Int) :
        Expression

    @Serializable
    @SerialName("forallE")
    data class ForallE(val name: Int, val type: Int, val body: Int, val binderInfo: BinderInfo, override val ie: Int) :
        Expression

    @Serializable
    @SerialName("letE")
    data class LetE(
        val name: Int,
        val type: Int,
        val value: Int,
        val body: Int,
        val nondep: Boolean,
        override val ie: Int
    ) : Expression

    @Serializable
    @SerialName("proj")
    data class Proj(val typeName: Int, val idx: Int, val struct: Int, override val ie: Int) : Expression

    @Serializable
    @SerialName("natVal")
    data class NatVal(val natVal: Int, override val ie: Int) : Expression

    @Serializable
    @SerialName("strVal")
    data class StrVal(val strVal: Int, override val ie: Int) : Expression

    @Serializable
    @SerialName("mdata")
    data class Mdata(val expr: Int, val data: JsonObject, override val ie: Int) : Expression
}

sealed interface Declaration : ExportType {
    @Serializable
    @SerialName("axiom")
    data class Axiom(val name: Int, val levelParams: List<Int>, val type: Int, val isUnsafe: Boolean) : Declaration

    @Serializable
    @SerialName("def")
    data class Def(
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val value: Int,
        // Can't put the serializer on `Hints` itself because it delegates to the default serializer
        @Serializable(with = HintsSerializer::class)
        val hints: Hints,
        val safety: Safety,
        val all: List<Int>
    ) : Declaration {
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
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val value: Int,
        val isUnsafe: Boolean,
        val all: List<Int>
    ) : Declaration

    @Serializable
    @SerialName("thm")
    data class Thm(
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val value: Int,
        val all: List<Int>
    ) : Declaration

    @Serializable
    @SerialName("quot")
    data class Quot(
        val name: Int,
        val levelParams: List<Int>,
        val type: Int,
        val kind: Kind,
    ) : Declaration {
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
}

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