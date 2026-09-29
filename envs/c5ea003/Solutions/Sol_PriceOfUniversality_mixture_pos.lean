-- Prove2me | solution 1 for PriceOfUniversality.mixture_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:34:41.193564+00:00
-- url     : https://prove2.me/submissions/d9cbbc15-8c3f-470f-b219-405f884f0fd9

-- Sol generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
/-
# The price of universality, II: minimax redundancy and mutual information

A *universal* code must serve every source in a class `{p θ}` with a single
length function `L`, whereas a *specialised* code may be tuned to one source.
The number of extra bits this costs is the **price of universality**.

Main results of this file, for a finite class `Θ` of sources on a finite
alphabet `A`:

* `kl_compensation` — the exact decomposition
  `∑ θ, π θ * D(p θ ‖ q) = I(π) + D(mixture ‖ q)`, valid for every coding
  distribution `q`. This is the algebraic heart of the redundancy-capacity
  theorem.
* `exists_source_redundancy_ge_mutualInfo` — **lower bound**: whatever code is
  used, some source in the class pays at least the mutual information `I(π)`
  of any prior `π`.
* `price_of_universality_upper` — **upper bound**: the Shannon code built from
  the mixture pays at most `log₂ |Θ| + 1` bits on *every* source of the class.
* `price_of_universality_sandwich` — for a class of `m` sources with pairwise
  disjoint supports the minimax redundancy is exactly `log₂ m`, up to one bit:
  `log₂ m ≤ minimax redundancy ≤ log₂ m + 1`.

The last statement is the promised closed form: the price of universality over
a class of `m` mutually distinguishable sources is `log₂ m` bits, i.e. exactly
the number of bits needed to name the source — no more and no less.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] {Θ : Type*} [Fintype Θ]

/-! ## Mixtures and mutual information -/






/-! ## The compensation identity -/


/-! ## The lower bound: universality costs at least the mutual information -/



/-! ## The upper bound: the mixture code -/




/-! ## Exact price for a class of mutually distinguishable sources -/





open PriceOfUniversality in
theorem solution{pri : Θ → ℝ} {p : Θ → A → ℝ} (hpri : ∀ θ, 0 ≤ pri θ)
    (hp : ∀ θ, IsPMF (p θ)) {θ₀ : Θ} {a : A} (h1 : 0 < pri θ₀) (h2 : 0 < p θ₀ a) :
    0 < mixture pri p a := by
  have hterm : 0 < pri θ₀ * p θ₀ a := mul_pos h1 h2
  refine lt_of_lt_of_le hterm ?_
  have hsub : ∑ θ ∈ ({θ₀} : Finset Θ), pri θ * p θ a ≤ ∑ θ, pri θ * p θ a := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro θ _ _
    exact mul_nonneg (hpri θ) ((hp θ).nonneg a)
  simpa using hsub
