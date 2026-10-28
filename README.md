# Kakeya4 Lean

四维挂谷猜想 Lean 4 形式化研究的结项源码，保留几何估计、测度论与 Fourier 分析组件；主定理形式化未完成。

Research sources from a discontinued Lean 4 formalization of the four-dimensional Kakeya conjecture, preserving reusable components in geometric inequalities, measure theory, and Fourier analysis.

Development ended on 2026-10-28 by the maintainer's decision following subsequent external mathematical developments. This is a source preservation snapshot; the incomplete formalization is retained as it stands. No further proof development is planned.

## Mathematical scope

- Finite weighted and finite-measure determinant multilinear Kakeya estimates.
- Semialgebraic selection, multiplicity, and slope-volume tools.
- Finite-scale multiplicative-convolution Fourier estimates and generated-law consumers.
- Weighted geometric sampling, observation laws, and semialgebraic density constructions.
- Preparatory finite-model reductions for restricted triple dot products.

The main theorem still contains a proof placeholder. Some manuscript statements are also placeholders, and integration of several independently checked components remains open. This repository is not a completed Lean verification of the four-dimensional theorem and is not an official OpenAI repository. Component-level checks must not be interpreted as a full-project proof certificate.

## Layout

- `Kakeya4/Foundation`: definitions and general tools.
- `Kakeya4/Construction`: geometric, combinatorial, and probabilistic constructions.
- `Kakeya4/Hard`: analytic inputs and compatibility libraries.
- `Kakeya4/Sec*.lean`: generated manuscript statement index.
- `Experiments`: additional source modules outside the default build.
- `Supplementary/ProjectionCompat`: original compatibility source assets outside the default build.
- `scripts`, `ir`, `blueprint`: build checks, statement metadata, and mathematical index.

## Validation at closure

The final packaging preserves proof/code tokens while removing internal process comments. The restricted-triple input package has a matching existing 86-module, 576-declaration verification receipt; the Fourier package retains its existing scoped verification. These are component results. No fresh complete Lean build or shared-integration acceptance is claimed for this final distribution. The main theorem and remaining statement placeholders are unchanged.

## Build

Lean is pinned to **4.34.0**, with Mathlib revision `56a9a88447f391672d7aeea117da03b6f7016b0d` locked by the manifest. Python 3 is needed for repository checks. A fresh machine must obtain these exact dependencies; no local compiled cache is distributed.

```sh
lake build
bash scripts/verify.sh
```

On Windows, use `powershell -NoProfile -File scripts/verify.ps1`. Verification uses `LEAN_NUM_THREADS=1`. The checks enforce the disclosed placeholder baseline as well as imports, dependency metadata, and axiom inventories; passing them alone does not mean the main theorem is proved.

## References and attribution

The principal manuscript is OpenAI's *Every Four-Dimensional Kakeya Set Has Full Hausdorff Dimension*. A pinned copy of its LaTeX sources is included under `vendor/openai-math`. Additional components adapt licensed community formalizations. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) and the accompanying license texts.
