plugins {
    alias(libs.plugins.kotlin.multiplatform)
}

group = "io.github.opletter.koda"
version = "0.0.1"

kotlin {
    jvm()
    js {
        browser()
        nodejs()
    }
}