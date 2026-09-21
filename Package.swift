// swift-tools-version: 6.0
import PackageDescription
import Foundation

// Release builds link each architecture against its matching Rust archive.
let rustLibraryPath = ProcessInfo.processInfo.environment["CHIPPYTEA_RUST_LIB_DIR"] ?? "target/release"

let package = Package(
    name: "chippytea",
    platforms: [.macOS(.v14)],
    dependencies: [
        .package(url: "https://github.com/sparkle-project/Sparkle", exact: "2.10.0")
    ],
    targets: [
        .systemLibrary(name: "ChippyteaCore", path: "native/Bridge"),
        .executableTarget(
            name: "chippytea",
            dependencies: ["ChippyteaCore", .product(name: "Sparkle", package: "Sparkle")],
            path: "native/Chippytea",
            linkerSettings: [
                .unsafeFlags(["-L\(rustLibraryPath)", "-lchippytea_core",
                              "-Xlinker", "-rpath", "-Xlinker", "@executable_path/../Frameworks"]),
                .linkedLibrary("sqlite3"),
                .linkedFramework("Security"),
                .linkedFramework("CoreServices")
            ])
    ],
    swiftLanguageModes: [.v5]
)
