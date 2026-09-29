-- Prove2me | solution 1 for PriceOfUniversality.kl_le_logb_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:07:23.466699+00:00
-- url     : https://prove2.me/submissions/c985c489-baf8-4613-9b04-fb353ba56f20

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
theorem solution[Nonempty Θ] {p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) (θ : Θ) :
    kl (p θ) (mixture (fun _ => (Fintype.card Θ : ℝ)⁻¹) p) ≤ logb 2 (Fintype.card Θ) := by
  set c : ℝ := (Fintype.card Θ : ℝ)⁻¹ with hc
  have hcard : (0:ℝ) < Fintype.card Θ := by
    exact_mod_cast Fintype.card_pos
  have hcpos : 0 < c := by positivity
  set m := mixture (fun _ => c) p with hmdef
  have hlb : ∀ a : A, c * p θ a ≤ m a := by
    intro a
    rw [hmdef, mixture]
    refine Finset.single_le_sum (f := fun θ' => c * p θ' a) ?_ (mem_univ θ)
    intro θ' _
    exact mul_nonneg hcpos.le ((hp θ').nonneg a)
  have hterm : ∀ a : A, p θ a * logb 2 (p θ a / m a) ≤ p θ a * logb 2 (Fintype.card Θ) := by
    intro a
    rcases eq_or_lt_of_le ((hp θ).nonneg a) with h | h
    · simp [← h]
    · have hma : 0 < m a := lt_of_lt_of_le (mul_pos hcpos h) (hlb a)
      have hratio : p θ a / m a ≤ (Fintype.card Θ : ℝ) := by
        rw [div_le_iff₀ hma]
        have h2 := mul_le_mul_of_nonneg_left (hlb a) hcard.le
        rw [hc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul] at h2
        linarith
      have hlog : logb 2 (p θ a / m a) ≤ logb 2 (Fintype.card Θ) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hratio
      exact mul_le_mul_of_nonneg_left hlog h.le
  calc kl (p θ) m = ∑ a, p θ a * logb 2 (p θ a / m a) := rfl
    _ ≤ ∑ a, p θ a * logb 2 (Fintype.card Θ) := Finset.sum_le_sum fun a _ => hterm a
    _ = logb 2 (Fintype.card Θ) := by rw [← Finset.sum_mul, (hp θ).total, one_mul]
