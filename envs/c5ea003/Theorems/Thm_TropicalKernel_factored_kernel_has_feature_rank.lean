-- Prove2me | Theorems.Thm_TropicalKernel_factored_kernel_has_feature_rank
-- name    : TropicalKernel.factored_kernel_has_feature_rank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:17.352313+00:00
-- url     : https://prove2.me/theorems/a7606eff-8166-4392-864a-4a7338543585
-- title:
--   Factored kernel has feature rank
-- statement:
--   Formal statement of `TropicalKernel.factored_kernel_has_feature_rank` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalKernel.factored_kernel_has_feature_rank(K : X → X → ℝ) (S : Finset X)
--       (hS : S.Nonempty) (φ : X → X → ℝ)
--       (hFact : ∀ x y : X, K x y = S.sup' hS (fun s => φ x s + φ y s)) :
--       TropicalFeatureRankLE K S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalKernelMeanDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalKernelMeanDuality.lean#L218

-- Thm stub generated from Bridges/TropicalKernelMeanDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalKernelMeanDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Kernel Mean Duality via Idempotent RKHS Semimodules

This file establishes a finite duality theorem at the interface of tropical
idempotent analysis and kernel-based machine learning. The central result shows
that finite tropical kernels with controlled feature complexity admit a canonical
idempotent reproducing semimodule whose extremal generators are exactly the
support prototypes needed for minimal classifier/regressor reconstruction.

## Mathematical Setting

We work over a finite type `X` with a tropical kernel `K : X → X → ℝ`.
In the tropical (max-plus) semiring, "addition" is `max` and "multiplication"
is `+`. A tropical kernel `K` admits a *feature factorization* of rank `r` if
there exists `φ : X → Fin r → ℝ` such that

  `K x y = max_{i : Fin r} (φ x i + φ y i)`

The *kernel semimodule* `H_K` is the set of functions `X → ℝ` that can be
represented as tropical linear combinations of kernel sections:

  `f(y) = max_{x ∈ S} (c x + K x y)`

for some finite support `S` and coefficients `c`.

## Main Results

* `residuatedCoefficient_le` — Residuated coefficients yield valid lower bounds
* `residuatedCoefficient_greatest` — Residuated coefficients are optimal
* `kernelSection_mem_span` — Every kernel section is self-representable
* `residuated_lower_bound` — The prototype predictor lower-bounds any target
* `reconstruction_exact_of_minimal_support` — Exact reconstruction from minimal support
* `minimal_support_is_antichain` — Minimal support sets are antichains
* `feature_rank_implies_generation` — Feature rank bounds generator size
* `generation_implies_feature_rank` — Generating sets bound feature rank
* `certified_residuated_bound` — Universal residuated lower bound

## References

- Akian, Gaubert, Kolokoltsov: "Idempotent analysis and max-plus algebra"
- Cohen, Gaubert, Quadrat: "Max-plus algebra and system theory"
-/

noncomputable section

open Finset

open TropicalKernel

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## §1. Tropical Kernel and Feature Factorization -/



/-! ## §2. Tropical Kernel Semimodule -/



/-! ## §3. Residuation -/


/-
The residuated coefficient gives a valid lower bound:
    `ResiduatedCoefficient K f x + K x y ≤ f y` for all `y`.
-/

/-
The residuated coefficient is the largest valid coefficient:
    if `c + K x y ≤ f y` for all `y`, then `c ≤ ResiduatedCoefficient K f x`.
-/


/-! ## §4. Domination and Antichains -/


/-! ## §5. Generation -/


/-! ## §6. Minimal Support -/



/-! ## §7. Core Lemmas -/

/-
Every kernel section is in the kernel span (self-represented via `{x}`).
-/

/-
**Residuated Lower Bound**: The residuated predictor always lower-bounds `f`.
-/

/-
**Reconstruction Exactness**: If `f` has a minimal support expansion,
    the predictor exactly reconstructs `f`.
-/

/-
**Minimal Support is Antichain**: If `S` minimally supports `f` and for
    each element there is a witness where it alone achieves the maximum,
    then `S` is a support antichain.
-/

/-
**Self-section residuation**: If `K x x ≥ K x y` for all `y`, then the
    residuated coefficient of `x` for `KernelSection K x` is `0`.
-/

/-! ## §8. Main Theorems -/

/-
**Theorem A**: Feature factorization of rank ≤ `r` implies existence of a
    generating set. The whole `Finset.univ` always generates.
-/

/-
**Theorem B**: If `K` factors through a set `S` (i.e., `K x y = max_{s∈S} (φ x s + φ y s)`
    for some function `φ`), then the feature rank is at most `|S|`.
-/

theorem TropicalKernel.factored_kernel_has_feature_rank(K : X → X → ℝ) (S : Finset X)
    (hS : S.Nonempty) (φ : X → X → ℝ)
    (hFact : ∀ x y : X, K x y = S.sup' hS (fun s => φ x s + φ y s)) :
    TropicalFeatureRankLE K S.card := by sorry
