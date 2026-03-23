package io.github.opletter.koda

import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.json.JsonDecoder
import kotlinx.serialization.json.JsonPrimitive
import kotlin.jvm.JvmInline

@Serializable(with = NatValueSerializer::class)
@JvmInline
value class NatValue private constructor(private val digits: String) : Comparable<NatValue> {
    fun isZero(): Boolean = digits == "0"

    fun compareTo(nonNegativeLong: Long): Int {
        require(nonNegativeLong >= 0L) { "Natural values cannot be compared with negative numbers" }
        return compareTo(fromLong(nonNegativeLong))
    }

    fun minus(nonNegativeLong: Long): NatValue {
        require(nonNegativeLong >= 0L) { "Natural values cannot subtract negative numbers" }
        if (nonNegativeLong == 0L) return this
        return this - fromLong(nonNegativeLong)
    }

    override fun compareTo(other: NatValue): Int = compareDecimalStrings(digits, other.digits)

    operator fun minus(other: NatValue): NatValue {
        require(this >= other) { "Natural subtraction underflow: $this - $other" }
        if (other.isZero()) return this
        if (this == other) return ZERO
        return NatValue(subtractDecimalStrings(digits, other.digits))
    }

    override fun toString(): String = digits

    companion object {
        val ZERO: NatValue = NatValue("0")

        fun fromString(raw: String): NatValue = NatValue(normalizeDecimal(raw))

        private fun fromLong(value: Long): NatValue {
            require(value >= 0L) { "Natural values cannot be negative" }
            return NatValue(value.toString())
        }

        private fun normalizeDecimal(raw: String): String {
            require(raw.isNotEmpty()) { "Expected non-empty nat literal" }
            require(raw.all { it in '0'..'9' }) { "Invalid nat literal '$raw': expected only digits" }
            return raw.trimStart('0').ifEmpty { "0" }
        }

        private fun compareDecimalStrings(left: String, right: String): Int {
            if (left.length != right.length) return left.length.compareTo(right.length)
            return left.compareTo(right)
        }

        private fun subtractDecimalStrings(left: String, right: String): String {
            val output = CharArray(left.length)
            var borrow = 0
            var leftIndex = left.length - 1
            var rightIndex = right.length - 1

            while (leftIndex >= 0) {
                val leftDigit = (left[leftIndex].code - '0'.code) - borrow
                val rightDigit = if (rightIndex >= 0) right[rightIndex].code - '0'.code else 0
                var diff = leftDigit - rightDigit
                if (diff < 0) {
                    diff += 10
                    borrow = 1
                } else {
                    borrow = 0
                }
                output[leftIndex] = ('0'.code + diff).toChar()
                leftIndex -= 1
                rightIndex -= 1
            }

            check(borrow == 0) { "Unexpected borrow after subtracting naturals: $left - $right" }
            return output.concatToString().trimStart('0').ifEmpty { "0" }
        }
    }
}

object NatValueSerializer : KSerializer<NatValue> {
    override val descriptor: SerialDescriptor =
        PrimitiveSerialDescriptor("NatValue", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: NatValue) {
        encoder.encodeString(value.toString())
    }

    override fun deserialize(decoder: Decoder): NatValue {
        return if (decoder is JsonDecoder) {
            val element = decoder.decodeJsonElement()
            val primitive = element as? JsonPrimitive
                ?: error("Expected natVal to be a JSON primitive, got ${element::class.simpleName}")
            NatValue.fromString(primitive.content)
        } else {
            NatValue.fromString(decoder.decodeString())
        }
    }
}
