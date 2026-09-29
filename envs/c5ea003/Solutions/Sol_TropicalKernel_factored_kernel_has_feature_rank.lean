-- Prove2me | solution 1 for TropicalKernel.factored_kernel_has_feature_rank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:29.579757+00:00
-- url     : https://prove2.me/submissions/4156ea7c-716d-44d2-83c3-c9eecdc8db36

-- Sol generated from Bridges/TropicalKernelMeanDuality.lean
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



open TropicalKernel in
theorem solution(K : X → X → ℝ) (S : Finset X)
    (hS : S.Nonempty) (φ : X → X → ℝ)
    (hFact : ∀ x y : X, K x y = S.sup' hS (fun s => φ x s + φ y s)) :
    TropicalFeatureRankLE K S.card := by
  have h_inj : Nonempty (S ≃ Fin S.card) := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
  obtain ⟨ e ⟩ := h_inj; use fun x i => if hi : i.val < S.card then φ x ( e.symm ⟨ i.val, hi ⟩ ) else φ x ( hS.choose ) ; simp +decide [ hFact ] ;
  intro x y; refine' le_antisymm _ _ <;> simp +decide [ Finset.sup'_le_iff ] ;
  · obtain ⟨ s, hs ⟩ := Finset.exists_max_image S ( fun s => φ x s + φ y s ) hS;
    use ⟨ e ⟨ s, hs.1 ⟩, by simp +decide ⟩ ; aesop;
  · -- By definition of $e$, we know that for any $b \in S$, there exists $i \in \{0, 1, ..., S.card - 1\}$ such that $e.symm i = b$.
    obtain ⟨b, hb⟩ : ∃ b ∈ S, ∀ s ∈ S, φ x s + φ y s ≤ φ x b + φ y b := by
      exact Finset.exists_max_image _ _ hS;
    refine' ⟨ b, hb.1, fun i => _ ⟩ ; split_ifs <;> simp_all +decide [ Finset.mem_univ, Finset.mem_image ] ;
    exact hb.2 _ hS.choose_spec
