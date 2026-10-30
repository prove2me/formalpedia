-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_succ_le_of_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:50:57.815325+00:00
-- url     : https://prove2.me/submissions/6c29135f-36a8-4a5c-b195-3900ba49679c

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
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

variable (i j : α)

/-- Coalesced common-minorant mass after `t` steps. -/
def rhovec : ℕ → α → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun z => (∑ a, rhovec t a * P a z)
      + ∑ x, ∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z

include hPnn hPmass in
/-- **Left marginal invariant:** `ρ_t + (U_t's left marginal) = t`-step law from `i`. -/
lemma left_marginal (t : ℕ) (z : α) :
    rhovec P rnk W i j t z + ∑ y, Umat P rnk W i j t z y = Mpow P t i z := by
  induction t generalizing z with
  | zero =>
    simp only [rhovec, Umat, Mpow, zero_add]
    by_cases hz : z = i
    · subst hz; simp
    · rw [if_neg (fun h => hz h.symm)]
      apply Finset.sum_eq_zero
      intro y _
      exact if_neg (fun h => hz h.1)
  | succ t ih =>
    have hU : ∑ y, Umat P rnk W i j (t + 1) z y
        = ∑ x, ∑ y, Umat P rnk W i j t x y * Lres P rnk W x y z := by
      simp only [Umat]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.mul_sum, Kres_left_marginal P rnk W hPnn hPmass x y z]
    rw [show Mpow P (t + 1) i z = ∑ a, Mpow P t i a * P a z from rfl]
    simp only [rhovec]
    rw [hU, add_assoc]
    rw [show (∑ x, ∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z)
        + ∑ x, ∑ y, Umat P rnk W i j t x y * Lres P rnk W x y z
        = ∑ x, (∑ y, Umat P rnk W i j t x y) * P x z from ?_]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← add_mul, ih a]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← mul_add]
      congr 1
      unfold Lres; ring

include hPmass in
lemma Mpow_mass (t : ℕ) (x : α) : ∑ z, Mpow P t x z = 1 := by
  induction t generalizing x with
  | zero =>
    simp only [Mpow]
    rw [Finset.sum_ite_eq Finset.univ x (fun _ => (1:ℝ)), if_pos (Finset.mem_univ x)]
  | succ t ih =>
    simp only [Mpow]
    rw [Finset.sum_comm, show (∑ z', ∑ z, Mpow P t x z' * P z' z) = ∑ z', Mpow P t x z' from
      Finset.sum_congr rfl (fun z' _ => by rw [← Finset.mul_sum, hPmass z', mul_one])]
    exact ih x

include hPnn hPmass in
lemma Umat_nonneg (t : ℕ) (a b : α) : 0 ≤ Umat P rnk W i j t a b := by
  induction t generalizing a b with
  | zero => simp only [Umat]; split <;> norm_num
  | succ t ih =>
    simp only [Umat]
    exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
      mul_nonneg (ih x y) (Kres_nonneg P rnk W hPnn hPmass x y a b)))

include hPnn hPmass in
lemma umass_eq (t : ℕ) : umass P rnk W i j t = 1 - ∑ z, rhovec P rnk W i j t z := by
  have hsum : ∑ z, (rhovec P rnk W i j t z + ∑ y, Umat P rnk W i j t z y) = ∑ z, Mpow P t i z :=
    Finset.sum_congr rfl (fun z _ => left_marginal P rnk W hPnn hPmass i j t z)
  rw [Finset.sum_add_distrib, Mpow_mass P hPmass t i] at hsum
  unfold umass
  linarith [hsum]

include hPmass in
lemma rho_succ_sum (t : ℕ) :
    ∑ z, rhovec P rnk W i j (t + 1) z
      = (∑ z, rhovec P rnk W i j t z) + ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
  simp only [rhovec]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => by rw [← Finset.mul_sum, hPmass a, mul_one])
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Finset.mul_sum]; rfl

include hPnn hPmass in
lemma umass_succ_eq (t : ℕ) :
    umass P rnk W i j (t + 1)
      = umass P rnk W i j t - ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
  rw [umass_eq P rnk W hPnn hPmass i j (t + 1), umass_eq P rnk W hPnn hPmass i j t,
    rho_succ_sum P rnk W hPmass i j t]
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: minorization on a sub-predicate ⟹ umass recursion

For the KILLED chain, the Doeblin minorization `δ ≤ cmass` holds only on the *active high-rank* window
`GoodHi` (where `Pker_window_minor`/brick 79 applies), NOT on absorbed/low-rank pairs.  This brick
generalizes the per-step contraction to any sub-predicate `Good` on which the minorization holds:

  `umass (t+1) ≤ umass t − δ · (Good-window mass of Umat t)`.

It follows from `umass_succ_eq` (`umass(t+1) = umass(t) − ∑ Umat·cmass`) since the coalescence mass
`∑ Umat·cmass ≥ δ · ∑_{Good} Umat`.  Then the (banked) CoalesceBridge consumes this with `g = ĝ` the
conditioned `Good`-fraction.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)
include hPnn hPmass in
theorem solution (Good : α → α → Prop) [DecidableRel Good] (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor_good : ∀ x y, Good x y → δ ≤ cmass P rnk W x y) (t : ℕ) :
    umass P rnk W i j (t + 1)
      ≤ umass P rnk W i j t
        - δ * ∑ x, ∑ y, (if Good x y then Umat P rnk W i j t x y else 0) := by
  rw [umass_succ_eq P rnk W hPnn hPmass i j t]
  have hge : δ * ∑ x, ∑ y, (if Good x y then Umat P rnk W i j t x y else 0)
      ≤ ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun y _ => ?_)
    by_cases hg : Good x y
    · rw [if_pos hg, mul_comm]
      exact mul_le_mul_of_nonneg_left (hminor_good x y hg) (Umat_nonneg P rnk W hPnn hPmass i j t x y)
    · rw [if_neg hg, mul_zero]
      exact mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j t x y) (cmass_nonneg P rnk W hPnn x y)
  linarith
