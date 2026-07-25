import io.github.opletter.koda.ExportTypeWrapper
import io.github.opletter.koda.typeCheck
import kotlinx.serialization.json.Json
import kotlin.io.path.Path
import kotlin.io.path.listDirectoryEntries
import kotlin.io.path.name
import kotlin.io.path.useLines

fun main(args: Array<String>) {
    runFile(Path(args[0]))
}

fun runFile(file: java.nio.file.Path) {
    file.useLines { lines ->
        typeCheck(lines.map { Json.decodeFromString<ExportTypeWrapper>(it).value })
    }
}

fun runTutorial(level: Int) {
    val file =
        (Path("../lean-arena-tests/bad/tutorial").listDirectoryEntries() + Path("../lean-arena-tests/good/tutorial").listDirectoryEntries())
            .find { it.name.startsWith(level.toString().padStart(3, '0')) } ?: error("File not found")
    println("Processing $file")
    val parsedData = file.useLines { lines ->
        lines.map { Json.decodeFromString<ExportTypeWrapper>(it).value }.toList()
    }

    val shouldSucceed = file.parent.parent.name == "good"
    var success = true
    try {
        typeCheck(parsedData.asSequence())
    } catch (e: Exception) {
        success = false
        if (shouldSucceed) {
            println("e: should have succeeded, but failed for $level")
            throw e
        } else {
            println("i: failed correctly for $level: ${e.message}")
        }
    } catch (e: NotImplementedError) {
        success = false
        println("e: ran into TODO for $level")
        throw e
    } finally {
        if (success && !shouldSucceed) throw Exception("e: should have failed, but succeeded for $level")
    }
}