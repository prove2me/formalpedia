-- Prove2me | solution 1 for PriceOfUniversality.average_redundancy_ge_mutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:40:10.994818+00:00
-- url     : https://prove2.me/submissions/f74ec276-bae5-4ffd-a023-7abc7db3ef7f

-- Sol generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Theorems.Thm_PriceOfUniversality_kl_compensation
import Theorems.Thm_PriceOfUniversality_kl_nonneg
import Theorems.Thm_PriceOfUniversality_mixture_isPMF
import Theorems.Thm_PriceOfUniversality_redundancy_eq_kl
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
theorem solution{pri : Θ → ℝ} {p : Θ → A → ℝ} {L : A → ℕ}
    (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
    (hL : IsCode L) :
    mutualInfo pri p ≤ ∑ θ, pri θ * redundancy (p θ) L := by
  set q : A → ℝ := fun a => ((2:ℝ)⁻¹) ^ (L a) with hqdef
  have hqpos : ∀ a, 0 < q a := fun a => by positivity
  have hred : ∀ θ : Θ, redundancy (p θ) L = kl (p θ) q :=
    fun θ => redundancy_eq_kl (hp θ) L
  have hcomp := kl_compensation hpri hpripos hp hqpos
  have hklnn : 0 ≤ kl (mixture pri p) q :=
    kl_nonneg (mixture_isPMF hpri hp) hqpos hL
  have : ∑ θ, pri θ * redundancy (p θ) L = ∑ θ, pri θ * kl (p θ) q :=
    Finset.sum_congr rfl fun θ _ => by rw [hred θ]
  rw [this, hcomp]
  linarith
