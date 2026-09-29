-- Prove2me | solution 1 for PriceOfUniversality.price_of_universality_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:22:31.13251+00:00
-- url     : https://prove2.me/submissions/c22c3dee-b25e-4c6b-a33a-6905a881c7e6

-- Sol generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Theorems.Thm_PriceOfUniversality_average_redundancy_ge_mutualInfo
import Theorems.Thm_PriceOfUniversality_mutualInfo_uniform_disjoint
import Theorems.Thm_PriceOfUniversality_price_of_universality_upper
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


/-- **Redundancy-capacity lower bound (minimax form).** Whatever universal code is
chosen, *some* source of the class pays at least `I(π)` bits of redundancy, for
every prior `π`. This is the price of universality. -/
theorem exists_source_redundancy_ge_mutualInfo [Nonempty Θ] {pri : Θ → ℝ} {p : Θ → A → ℝ}
    {L : A → ℕ} (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
    (hL : IsCode L) :
    ∃ θ : Θ, mutualInfo pri p ≤ redundancy (p θ) L := by
  obtain ⟨θ₀, -, hmax⟩ :=
    Finset.exists_max_image (univ : Finset Θ) (fun θ => redundancy (p θ) L)
      (univ_nonempty)
  refine ⟨θ₀, le_trans (average_redundancy_ge_mutualInfo hpri hpripos hp hL) ?_⟩
  calc ∑ θ, pri θ * redundancy (p θ) L
      ≤ ∑ _θ : Θ, pri _θ * redundancy (p θ₀) L := by
        refine Finset.sum_le_sum fun θ _ => ?_
        exact mul_le_mul_of_nonneg_left (hmax θ (mem_univ θ)) (hpri.nonneg θ)
    _ = redundancy (p θ₀) L := by rw [← Finset.sum_mul, hpri.total, one_mul]

/-! ## The upper bound: the mixture code -/




/-! ## Exact price for a class of mutually distinguishable sources -/





open PriceOfUniversality in
theorem solution[Nonempty Θ] {p : Θ → A → ℝ}
    (hp : ∀ θ, IsPMF (p θ)) (hdisj : DisjointSupports p)
    (hcov : ∀ a : A, 0 < mixture (fun _ => (Fintype.card Θ : ℝ)⁻¹) p a) :
    (∀ L : A → ℕ, IsCode L → ∃ θ, logb 2 (Fintype.card Θ) ≤ redundancy (p θ) L) ∧
    (∃ L : A → ℕ, IsCode L ∧ ∀ θ, redundancy (p θ) L ≤ logb 2 (Fintype.card Θ) + 1) := by
  constructor
  · intro L hL
    have hcard : (0:ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
    have hpri : IsPMF (fun _ : Θ => (Fintype.card Θ : ℝ)⁻¹) := by
      refine ⟨fun _ => by positivity, ?_⟩
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp
    obtain ⟨θ, hθ⟩ :=
      exists_source_redundancy_ge_mutualInfo (pri := fun _ => (Fintype.card Θ : ℝ)⁻¹)
        hpri (fun _ => by positivity) hp hL
    rw [mutualInfo_uniform_disjoint hp hdisj] at hθ
    exact ⟨θ, hθ⟩
  · exact price_of_universality_upper hp hcov
