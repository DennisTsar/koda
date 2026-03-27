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

    fun plus(nonNegativeLong: Long): NatValue {
        require(nonNegativeLong >= 0L) { "Natural values cannot add negative numbers" }
        if (nonNegativeLong == 0L) return this
        return this + fromLong(nonNegativeLong)
    }

    operator fun plus(other: NatValue): NatValue {
        if (this.isZero()) return other
        if (other.isZero()) return this
        return NatValue(addDecimalStrings(digits, other.digits))
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

    operator fun times(other: NatValue): NatValue {
        if (this.isZero() || other.isZero()) return ZERO
        if (this == ONE) return other
        if (other == ONE) return this
        return NatValue(multiplyDecimalStrings(digits, other.digits))
    }

    fun divMod(other: NatValue): Pair<NatValue, NatValue> {
        require(!other.isZero()) { "Natural division by zero is undefined for divMod" }
        if (this.isZero()) return ZERO to ZERO
        if (other == ONE) return this to ZERO
        if (this < other) return ZERO to this
        val lhsLong = this.toLongOrNull()
        val rhsLong = other.toLongOrNull()
        if (lhsLong != null && rhsLong != null) {
            return fromLong(lhsLong / rhsLong) to fromLong(lhsLong % rhsLong)
        }
        val quotientAndRemainder = divideDecimalStrings(this.digits, other.digits)
        return NatValue(quotientAndRemainder.first) to NatValue(quotientAndRemainder.second)
    }

    fun divLean(other: NatValue): NatValue {
        if (other.isZero()) return ZERO
        return divMod(other).first
    }

    fun modLean(other: NatValue): NatValue {
        if (other.isZero()) return this
        return divMod(other).second
    }

    fun pow(exponent: Int): NatValue {
        require(exponent >= 0) { "Natural powers cannot have negative exponents" }
        if (exponent == 0) return ONE
        if (this.isZero()) return ZERO
        var remainingExp = exponent
        var base = this
        var acc = ONE
        while (remainingExp > 0) {
            if ((remainingExp and 1) != 0) {
                acc *= base
            }
            remainingExp = remainingExp ushr 1
            if (remainingExp != 0) {
                base *= base
            }
        }
        return acc
    }

    fun toLongOrNull(): Long? {
        if (digits.length > Long.MAX_VALUE.toString().length) return null
        val parsed = digits.toLongOrNull() ?: return null
        return if (parsed >= 0L) parsed else null
    }

    fun toIntOrNull(): Int? {
        val longValue = toLongOrNull() ?: return null
        if (longValue > Int.MAX_VALUE.toLong()) return null
        return longValue.toInt()
    }

    override fun toString(): String = digits

    companion object {
        val ZERO: NatValue = NatValue("0")
        val ONE: NatValue = NatValue("1")

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

        private fun addDecimalStrings(left: String, right: String): String {
            val maxLength = maxOf(left.length, right.length)
            val output = CharArray(maxLength + 1)
            var leftIndex = left.length - 1
            var rightIndex = right.length - 1
            var outIndex = output.size - 1
            var carry = 0

            while (outIndex >= 0) {
                val leftDigit = if (leftIndex >= 0) left[leftIndex] - '0' else 0
                val rightDigit = if (rightIndex >= 0) right[rightIndex] - '0' else 0
                val sum = leftDigit + rightDigit + carry
                output[outIndex] = ('0'.code + (sum % 10)).toChar()
                carry = sum / 10
                leftIndex -= 1
                rightIndex -= 1
                outIndex -= 1
            }

            return output.concatToString().trimStart('0').ifEmpty { "0" }
        }

        private fun subtractDecimalStrings(left: String, right: String): String {
            val output = CharArray(left.length)
            var borrow = 0
            var leftIndex = left.length - 1
            var rightIndex = right.length - 1

            while (leftIndex >= 0) {
                val leftDigit = (left[leftIndex] - '0') - borrow
                val rightDigit = if (rightIndex >= 0) right[rightIndex] - '0' else 0
                var diff = leftDigit - rightDigit
                if (diff < 0) {
                    diff += 10
                    borrow = 1
                } else {
                    borrow = 0
                }
                output[leftIndex] = '0' + diff
                leftIndex -= 1
                rightIndex -= 1
            }

            check(borrow == 0) { "Unexpected borrow after subtracting naturals: $left - $right" }
            return output.concatToString().trimStart('0').ifEmpty { "0" }
        }

        private fun multiplyDecimalStrings(left: String, right: String): String {
            val result = IntArray(left.length + right.length)
            var leftIndex = left.length - 1
            while (leftIndex >= 0) {
                val leftDigit = left[leftIndex] - '0'
                var carry = 0
                var rightIndex = right.length - 1
                while (rightIndex >= 0) {
                    val rightDigit = right[rightIndex] - '0'
                    val resultIndex = leftIndex + rightIndex + 1
                    val total = leftDigit * rightDigit + result[resultIndex] + carry
                    result[resultIndex] = total % 10
                    carry = total / 10
                    rightIndex -= 1
                }
                result[leftIndex] += carry
                leftIndex -= 1
            }

            val output = CharArray(result.size)
            result.indices.forEach { index ->
                output[index] = ('0'.code + result[index]).toChar()
            }
            return output.concatToString().trimStart('0').ifEmpty { "0" }
        }

        private fun multiplyDecimalStringByDigit(value: String, digit: Int): String {
            require(digit in 0..9) { "Expected decimal digit in 0..9, got $digit" }
            if (digit == 0) return "0"
            if (digit == 1) return value
            val output = CharArray(value.length + 1)
            var carry = 0
            var inIndex = value.length - 1
            var outIndex = output.size - 1
            while (inIndex >= 0) {
                val product = (value[inIndex] - '0') * digit + carry
                output[outIndex] = ('0'.code + (product % 10)).toChar()
                carry = product / 10
                inIndex -= 1
                outIndex -= 1
            }
            output[outIndex] = ('0'.code + carry).toChar()
            return output.concatToString().trimStart('0').ifEmpty { "0" }
        }

        private fun divideDecimalStrings(dividend: String, divisor: String): Pair<String, String> {
            require(divisor != "0") { "Division by zero" }
            val compare = compareDecimalStrings(dividend, divisor)
            if (compare < 0) return "0" to dividend
            if (divisor == "1") return dividend to "0"

            val quotient = StringBuilder(dividend.length)
            var remainder = "0"
            for (digitChar in dividend) {
                remainder = if (remainder == "0") {
                    digitChar.toString()
                } else {
                    "$remainder$digitChar"
                }.trimStart('0').ifEmpty { "0" }

                var quotientDigit = 0
                var quotientDigitProduct = "0"
                for (candidate in 9 downTo 1) {
                    val product = multiplyDecimalStringByDigit(divisor, candidate)
                    if (compareDecimalStrings(product, remainder) <= 0) {
                        quotientDigit = candidate
                        quotientDigitProduct = product
                        break
                    }
                }
                if (quotientDigit != 0) {
                    remainder = subtractDecimalStrings(remainder, quotientDigitProduct)
                }
                quotient.append(('0'.code + quotientDigit).toChar())
            }
            return quotient.toString().trimStart('0').ifEmpty { "0" } to remainder
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