-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.greenT_le_T
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:07:34.541986+00:00
-- url     : https://prove2.me/submissions/f468116b-cce4-4fe8-9e22-14029c32a0b2

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERGreenT
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: the deterministic windowed-coupling ITER (finite-sum algebra)

The renewal-alignment overlap bound, built WITHOUT any probabilistic coupling library — purely as
finite-sum recursion over a finite state type `α` with a stochastic kernel `P`.  We track the coalesced
common-minorant mass `ρ_t` and the unmatched pair mass `U_t`; the marginal invariant
`ρ_t z + ∑_y U_t z y = Pⁿ i z` makes `ρ_t` a common minorant of the two `t`-step laws, so
`∑ ρ_t ≤ overlap`.  The unmatched mass contracts: `u_{t+1} ≤ (1−δ) u_t + δ b_t` with `b_t` the unmatched
mass outside the rank window.  Hence

  `overlap(Pᵐ i ·, Pᵐ j ·) ≥ 1 − (1−δ)^m − δ·∑_{t<m} (1−δ)^{m−t−1} b_t`.

The lone analytic input left is the bad-mass bound `b_t ≤ e_t`.  Opus-authored (construction ChatGPT R3).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn in
lemma Cpart_nonneg (x y z : α) : 0 ≤ Cpart P rnk W x y z := by
  unfold Cpart; split
  · exact le_min (hPnn x z) (hPnn y z)
  · exact le_refl 0

include hPnn in
lemma Cpart_le_left (x y z : α) : Cpart P rnk W x y z ≤ P x z := by
  unfold Cpart; split
  · exact min_le_left _ _
  · exact hPnn x z

include hPnn in
lemma Cpart_le_right (x y z : α) : Cpart P rnk W x y z ≤ P y z := by
  unfold Cpart; split
  · exact min_le_right _ _
  · exact hPnn y z

include hPnn in
lemma Lres_nonneg (x y z : α) : 0 ≤ Lres P rnk W x y z := by
  unfold Lres; linarith [Cpart_le_left P rnk W hPnn x y z]

include hPnn in
lemma Rres_nonneg (x y z : α) : 0 ≤ Rres P rnk W x y z := by
  unfold Rres; linarith [Cpart_le_right P rnk W hPnn x y z]

include hPnn hPmass in
lemma cmass_le_one (x y : α) : cmass P rnk W x y ≤ 1 := by
  unfold cmass
  calc ∑ z, Cpart P rnk W x y z ≤ ∑ z, P x z :=
        Finset.sum_le_sum (fun z _ => Cpart_le_left P rnk W hPnn x y z)
    _ = 1 := hPmass x

include hPnn in
lemma cmass_nonneg (x y : α) : 0 ≤ cmass P rnk W x y :=
  Finset.sum_nonneg (fun z _ => Cpart_nonneg P rnk W hPnn x y z)

include hPmass in
lemma Lres_sum (x y : α) : ∑ z, Lres P rnk W x y z = 1 - cmass P rnk W x y := by
  unfold Lres cmass
  rw [Finset.sum_sub_distrib, hPmass x]

include hPmass in
lemma Rres_sum (x y : α) : ∑ z, Rres P rnk W x y z = 1 - cmass P rnk W x y := by
  unfold Rres cmass
  rw [Finset.sum_sub_distrib, hPmass y]

include hPnn hPmass in
lemma Kres_nonneg (x y a b : α) : 0 ≤ Kres P rnk W x y a b := by
  unfold Kres; split
  · rename_i h
    exact div_nonneg (mul_nonneg (Lres_nonneg P rnk W hPnn x y a) (Rres_nonneg P rnk W hPnn x y b))
      (by linarith)
  · exact le_refl 0

include hPnn hPmass in
lemma Kres_left_marginal (x y a : α) : ∑ b, Kres P rnk W x y a b = Lres P rnk W x y a := by
  unfold Kres
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    have hne : (1 - cmass P rnk W x y) ≠ 0 := by linarith
    rw [← Finset.sum_div, ← Finset.mul_sum, Rres_sum P rnk W hPmass,
      mul_div_assoc, div_self hne, mul_one]
  · simp only [if_neg h, Finset.sum_const_zero]
    have hc1 : cmass P rnk W x y = 1 := le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    have hL0 : ∑ z, Lres P rnk W x y z = 0 := by rw [Lres_sum P rnk W hPmass, hc1]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Lres_nonneg P rnk W hPnn x y z)).mp hL0
    exact (this a (Finset.mem_univ a)).symm

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Conditioned residual kernel

`Kres` is the substochastic residual product kernel whose row mass is `1 - cmass`.
This file normalizes it to a stochastic conditioned-residual kernel.  Rows with
`cmass = 1` are parked at the current pair; the analytic application only uses
the `cmass < 1` rows, but the parked rows make the pair kernel stochastic
globally.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
lemma Kres_sum (x y : α) :
    ∑ a, ∑ b, Kres P rnk W x y a b = 1 - cmass P rnk W x y := by
  calc
    ∑ a, ∑ b, Kres P rnk W x y a b
        = ∑ a, Lres P rnk W x y a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          exact Kres_left_marginal P rnk W hPnn hPmass x y a
    _ = 1 - cmass P rnk W x y := Lres_sum P rnk W hPmass x y

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Green potential bounds (renewal route B capstone support)

`greenT` (ITERGreenT) is the finite-horizon expected window occupation under the substochastic
residual kernel `Kres` (row sum `1 − cmass ≤ 1`).  This file banks the elementary upper bound
`greenT ≤ T` (each residual iterate of the window indicator is `≤ 1`).  The matching lower bound
`greenT ≥ c√T` (`greenT_lower_fixed_window`) is the lone analytic wall (see `DOCTRINE-walls.md`).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
/-- Each residual iterate of the window indicator is `≤ 1` (substochastic `Kres`). -/
lemma KresIter_le_one (t : ℕ) :
    ∀ x y, (KresAct P rnk W)^[t] (goodIndic rnk W) x y ≤ 1 := by
  induction t with
  | zero =>
      intro x y
      simp only [Function.iterate_zero, id_eq, goodIndic]
      split <;> norm_num
  | succ t ih =>
      intro x y
      rw [Function.iterate_succ', Function.comp_apply]
      calc KresAct P rnk W ((KresAct P rnk W)^[t] (goodIndic rnk W)) x y
          = ∑ a, ∑ b, Kres P rnk W x y a b
              * (KresAct P rnk W)^[t] (goodIndic rnk W) a b := rfl
        _ ≤ ∑ a, ∑ b, Kres P rnk W x y a b * 1 := by
            refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
            exact mul_le_mul_of_nonneg_left (ih a b) (Kres_nonneg P rnk W hPnn hPmass x y a b)
        _ = ∑ a, ∑ b, Kres P rnk W x y a b := by simp
        _ = 1 - cmass P rnk W x y := Kres_sum P rnk W hPnn hPmass x y
        _ ≤ 1 := by linarith [cmass_nonneg P rnk W hPnn x y]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
include hPnn hPmass in
theorem solution (T : ℕ) (x y : α) : greenT P rnk W T x y ≤ (T : ℝ) := by
  unfold greenT
  calc ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t] (goodIndic rnk W) x y
      ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => KresIter_le_one P rnk W hPnn hPmass t x y)
    _ = (T : ℝ) := by simp
