import org.jetbrains.kotlin.gradle.ExperimentalKotlinGradlePluginApi

plugins {
    alias(libs.plugins.kotlin.multiplatform)
    alias(libs.plugins.kotlinx.serialization)
}

group = "io.github.opletter.koda"
version = "0.0.1"

kotlin {
    @OptIn(ExperimentalKotlinGradlePluginApi::class)
    dependencies {
        implementation(libs.kotlinx.serialization.json)
    }

    jvm()
    js {
        browser()
        nodejs()
    }

    compilerOptions {
//        languageVersion = KotlinVersion.KOTLIN_2_4
        freeCompilerArgs.addAll(
            "-Xreturn-value-checker=full",
            "-Xcontext-parameters",
            "-Xname-based-destructuring=complete",
//            "-Xexplicit-context-arguments"
        )
    }
}