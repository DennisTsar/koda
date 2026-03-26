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

    fun saturatingMinus(other: NatValue): NatValue {
        return if (this >= other) this - other else ZERO
    }

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

    fun div(other: NatValue): NatValue {
        if (other.isZero()) return ZERO
        if (this < other) return ZERO
        return NatValue(divideDecimalStrings(digits, other.digits).first)
    }

    fun mod(other: NatValue): NatValue {
        if (other.isZero()) return this
        if (this < other) return this
        return NatValue(divideDecimalStrings(digits, other.digits).second)
    }

    fun pow(exponent: NatValue): NatValue {
        if (exponent.isZero()) return ONE
        if (this.isZero()) return ZERO

        var result = ONE
        var base = this
        var expDigits = exponent.digits
        while (expDigits != "0") {
            if (isDecimalStringOdd(expDigits)) {
                result *= base
            }
            expDigits = divideDecimalStringByTwo(expDigits)
            if (expDigits != "0") {
                base *= base
            }
        }
        return result
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
            var carry = 0
            var leftIndex = left.length - 1
            var rightIndex = right.length - 1
            var outIndex = maxLength

            while (outIndex >= 0) {
                val leftDigit = if (leftIndex >= 0) left[leftIndex] - '0' else 0
                val rightDigit = if (rightIndex >= 0) right[rightIndex] - '0' else 0
                val sum = leftDigit + rightDigit + carry
                output[outIndex] = ('0'.code + (sum % 10)).toChar()
                carry = sum / 10
                outIndex -= 1
                leftIndex -= 1
                rightIndex -= 1
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
            val output = IntArray(left.length + right.length)
            var leftIndex = left.length - 1
            while (leftIndex >= 0) {
                val leftDigit = left[leftIndex] - '0'
                var rightIndex = right.length - 1
                while (rightIndex >= 0) {
                    val rightDigit = right[rightIndex] - '0'
                    val outIndex = leftIndex + rightIndex + 1
                    val product = leftDigit * rightDigit + output[outIndex]
                    output[outIndex] = product % 10
                    output[outIndex - 1] += product / 10
                    rightIndex -= 1
                }
                leftIndex -= 1
            }
            return output.joinToString(separator = "").trimStart('0').ifEmpty { "0" }
        }

        private fun multiplyDecimalStringByDigit(value: String, digit: Int): String {
            require(digit in 0..9) { "Expected single digit multiplier, got $digit" }
            if (digit == 0 || value == "0") return "0"
            if (digit == 1) return value
            val output = CharArray(value.length + 1)
            var carry = 0
            var valueIndex = value.length - 1
            var outIndex = output.size - 1
            while (valueIndex >= 0) {
                val product = (value[valueIndex] - '0') * digit + carry
                output[outIndex] = ('0'.code + (product % 10)).toChar()
                carry = product / 10
                valueIndex -= 1
                outIndex -= 1
            }
            output[outIndex] = ('0'.code + carry).toChar()
            return output.concatToString().trimStart('0').ifEmpty { "0" }
        }

        private fun appendDigit(value: String, digit: Char): String {
            require(digit in '0'..'9') { "Expected digit, got '$digit'" }
            if (value == "0") return digit.toString()
            return value + digit
        }

        private fun divideDecimalStrings(dividend: String, divisor: String): Pair<String, String> {
            require(divisor != "0") { "Cannot divide by zero in natural numbers" }
            if (compareDecimalStrings(dividend, divisor) < 0) return "0" to dividend

            val quotient = StringBuilder(dividend.length)
            var remainder = "0"
            for (digit in dividend) {
                remainder = appendDigit(remainder, digit)
                if (compareDecimalStrings(remainder, divisor) < 0) {
                    quotient.append('0')
                    continue
                }

                var low = 1
                var high = 9
                while (low <= high) {
                    val mid = (low + high) ushr 1
                    val midProduct = multiplyDecimalStringByDigit(divisor, mid)
                    if (compareDecimalStrings(midProduct, remainder) <= 0) {
                        low = mid + 1
                    } else {
                        high = mid - 1
                    }
                }
                val quotientDigit = high
                quotient.append(('0'.code + quotientDigit).toChar())
                val subtraction = multiplyDecimalStringByDigit(divisor, quotientDigit)
                remainder = subtractDecimalStrings(remainder, subtraction)
            }
            return normalizeDecimal(quotient.toString()) to normalizeDecimal(remainder)
        }

        private fun isDecimalStringOdd(value: String): Boolean {
            val lastDigit = value.last() - '0'
            return (lastDigit and 1) == 1
        }

        private fun divideDecimalStringByTwo(value: String): String {
            var carry = 0
            val output = CharArray(value.length)
            value.forEachIndexed { index, char ->
                val current = carry * 10 + (char - '0')
                output[index] = ('0'.code + (current / 2)).toChar()
                carry = current % 2
            }
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
