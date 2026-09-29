-- Prove2me | solution 1 for PriceOfUniversality.mixture_isPMF
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:38.609165+00:00
-- url     : https://prove2.me/submissions/d8335e12-1467-4138-b47a-b2242b169fdf

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



lemma mixture_nonneg {pri : Θ → ℝ} {p : Θ → A → ℝ} (hpri : ∀ θ, 0 ≤ pri θ)
    (hp : ∀ θ, IsPMF (p θ)) (a : A) : 0 ≤ mixture pri p a :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (hpri θ) ((hp θ).nonneg a)



/-! ## The compensation identity -/


/-! ## The lower bound: universality costs at least the mutual information -/



/-! ## The upper bound: the mixture code -/




/-! ## Exact price for a class of mutually distinguishable sources -/





open PriceOfUniversality in
theorem solution{pri : Θ → ℝ} {p : Θ → A → ℝ} (hpri : IsPMF pri)
    (hp : ∀ θ, IsPMF (p θ)) : IsPMF (mixture pri p) := by
  refine ⟨mixture_nonneg hpri.nonneg hp, ?_⟩
  simp only [mixture]
  rw [Finset.sum_comm]
  have : ∀ θ : Θ, ∑ a, pri θ * p θ a = pri θ := by
    intro θ; rw [← Finset.mul_sum, (hp θ).total, mul_one]
  calc ∑ θ, ∑ a, pri θ * p θ a = ∑ θ, pri θ := Finset.sum_congr rfl fun θ _ => this θ
    _ = 1 := hpri.total
