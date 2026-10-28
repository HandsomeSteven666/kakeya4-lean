# Projection compatibility source collection

Source assets retained at project closure, including local analytic adapters and adapted OpenAI/math sources. The upstream revision is `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, under Apache-2.0. Copyright headers and the upstream license are preserved. Local changes adapt imports, proofs and resource settings for Lean 4.34.0 and the pinned Mathlib.

These original `OAI.*` module paths are preserved for source recovery. This directory is outside the default library build and is not an independent Lake package: some imports require the pinned upstream source tree and the project's `Kakeya4` modules. The production compatibility bundles are under `Kakeya4/Hard/OSSCompat`; do not import both versions into one environment. Retention here does not assert new whole-project compilation or main-theorem integration.
