-- Prove2me | solution 1 for PriceOfUniversality.price_of_universality_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:17:50.611234+00:00
-- url     : https://prove2.me/submissions/a6d0a5e7-d6f5-4551-bfe5-887b730c3981

-- Sol generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Theorems.Thm_PriceOfUniversality_IsPMF_le_one
import Theorems.Thm_PriceOfUniversality_kl_le_logb_card
import Theorems.Thm_PriceOfUniversality_mixture_code_redundancy_le
import Theorems.Thm_PriceOfUniversality_mixture_isPMF
import Theorems.Thm_PriceOfUniversality_shannonCode_isCode
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
theorem solution[Nonempty Θ] {p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hcov : ∀ a : A, 0 < mixture (fun _ => (Fintype.card Θ : ℝ)⁻¹) p a) :
    ∃ L : A → ℕ, IsCode L ∧ ∀ θ, redundancy (p θ) L ≤ logb 2 (Fintype.card Θ) + 1 := by
  set c : ℝ := (Fintype.card Θ : ℝ)⁻¹ with hc
  set m := mixture (fun _ => c) p with hmdef
  have hcard : (0:ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
  have hmpmf : IsPMF m := by
    refine mixture_isPMF ⟨fun _ => by positivity, ?_⟩ hp
    rw [Finset.sum_const, nsmul_eq_mul, hc, Finset.card_univ]
    field_simp
  refine ⟨shannonCode m, shannonCode_isCode hmpmf hcov, fun θ => ?_⟩
  have h1 := mixture_code_redundancy_le (hp θ) hcov hmpmf.le_one
  have h2 := kl_le_logb_card hp θ
  rw [← hmdef] at h2
  linarith
