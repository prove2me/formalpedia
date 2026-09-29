-- Prove2me | Definitions.Def_Bridges_TropicalKernelMeanDuality
-- name    : Bridges_TropicalKernelMeanDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:31.948143+00:00
-- url     : https://prove2.me/theorems/6780323d-cc65-4660-8209-9ad9ed316dae
-- title:
--   Aether Catalog definitions — Bridges_TropicalKernelMeanDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalKernelMeanDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalKernelMeanDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalKernel

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## §1. Tropical Kernel and Feature Factorization -/

/-- A kernel section `K_x` is the function `y ↦ K x y`. -/
def KernelSection (K : X → X → ℝ) (x : X) : X → ℝ := K x

/-- A kernel `K` has a tropical feature factorization of rank ≤ `r` through
    an index type `I` with `|I| ≤ r`. We use `Fin r` as the index type and
    require `r > 0` for nonemptiness. -/
def TropicalFeatureRankLE (K : X → X → ℝ) (r : ℕ) : Prop :=
  ∃ φ : X → Fin (r + 1) → ℝ,
    ∀ x y : X, K x y = (Finset.univ (α := Fin (r + 1))).sup'
      univ_nonempty (fun i => φ x i + φ y i)

/-! ## §2. Tropical Kernel Semimodule -/

/-- A function `f : X → ℝ` is *represented by* kernel sections from a nonempty
    set `S` with coefficients `c` if `f y = max_{x ∈ S} (c x + K x y)` for all `y`. -/
def IsRepresentedBy (K : X → X → ℝ) (f : X → ℝ) (S : Finset X)
    (hS : S.Nonempty) (c : X → ℝ) : Prop :=
  ∀ y : X, f y = S.sup' hS (fun x => c x + K x y)

/-- A function `f : X → ℝ` is *in the kernel span* if there exists a nonempty
    support `S` and coefficients `c` representing it. -/
def InKernelSpan (K : X → X → ℝ) (f : X → ℝ) : Prop :=
  ∃ (S : Finset X) (hS : S.Nonempty) (c : X → ℝ), IsRepresentedBy K f S hS c

/-! ## §3. Residuation -/

/-- The *residuated coefficient* of `x` for representing `f` via kernel section
    `K x`: the largest `c` such that `c + K x y ≤ f y` for all `y`.
    This is `min_y (f y - K x y)`, the tropical residuation. -/
def ResiduatedCoefficient (K : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (Finset.univ (α := X)).inf' univ_nonempty (fun y => f y - K x y)

/-
The residuated coefficient gives a valid lower bound:
    `ResiduatedCoefficient K f x + K x y ≤ f y` for all `y`.
-/

/-
The residuated coefficient is the largest valid coefficient:
    if `c + K x y ≤ f y` for all `y`, then `c ≤ ResiduatedCoefficient K f x`.
-/

/-- An element `x` is in the *active support* of `f` if the residuated
    representation through `x` is tight at some point. -/
def IsActiveSupport (K : X → X → ℝ) (f : X → ℝ) (x : X) : Prop :=
  ∃ y : X, ResiduatedCoefficient K f x + K x y = f y

/-! ## §4. Domination and Antichains -/

/-- A set `T` is a *support antichain* for `f` if no element's residuated
    contribution is pointwise dominated by another element's contribution. -/
def IsSupportAntichain (K : X → X → ℝ) (f : X → ℝ) (T : Finset X) : Prop :=
  ∀ x ∈ T, ∀ z ∈ T, x ≠ z →
    ¬(∀ y : X, ResiduatedCoefficient K f x + K x y ≤
                ResiduatedCoefficient K f z + K z y)

/-! ## §5. Generation -/

/-- A nonempty set `S` *generates* the kernel semimodule: every kernel section
    is bounded above by some tropical combination from `S`. -/
def GeneratesKernelSemimodule (K : X → X → ℝ) (S : Finset X) (hS : S.Nonempty) : Prop :=
  ∀ z : X, ∃ c : X → ℝ,
    ∀ y : X, K z y ≤ S.sup' hS (fun x => c x + K x y)

/-! ## §6. Minimal Support -/

/-- A set `S` *minimally supports* `f` using residuated coefficients:
    `f` equals the tropical combination and every element is active. -/
def MinimalSupportExpansion (K : X → X → ℝ) (f : X → ℝ) (S : Finset X)
    (hS : S.Nonempty) : Prop :=
  (∀ y : X, f y = S.sup' hS (fun x => ResiduatedCoefficient K f x + K x y)) ∧
  (∀ x ∈ S, IsActiveSupport K f x)

/-- The *tropical prototype predictor* reconstructed from a support set. -/
def TropicalPrototypePredictor (K : X → X → ℝ) (f : X → ℝ) (S : Finset X)
    (hS : S.Nonempty) : X → ℝ :=
  fun y => S.sup' hS (fun x => ResiduatedCoefficient K f x + K x y)

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

/-
**Theorem C**: For any function, all residuated coefficients provide valid
    lower bounds. This is the universal residuated approximation guarantee.
-/

/-
**Theorem D**: The residuated coefficient is tight: the infimum is achieved.
-/

/-
**Corollary**: Every `x` is in the active support of `f` with respect to
    the residuation — the infimum defining the residuated coefficient is achieved.
-/

end TropicalKernel

end


