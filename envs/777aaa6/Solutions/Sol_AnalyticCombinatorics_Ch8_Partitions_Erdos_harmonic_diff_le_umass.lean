-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.harmonic_diff_le_umass
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:39:00.649205+00:00
-- url     : https://prove2.me/submissions/115d03e8-b1bc-4f13-9c7e-cca84922604d

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

/-- Overlap (shared mass) of two mass vectors. -/
def overlap (μ ν : α → ℝ) : ℝ := ∑ z, min (μ z) (ν z)

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

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

include hPnn hPmass in
lemma Kres_right_marginal (x y b : α) : ∑ a, Kres P rnk W x y a b = Rres P rnk W x y b := by
  unfold Kres
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    have hne : (1 - cmass P rnk W x y) ≠ 0 := by linarith
    rw [← Finset.sum_div, ← Finset.sum_mul, Lres_sum P rnk W hPmass,
      mul_comm, mul_div_assoc, div_self hne, mul_one]
  · simp only [if_neg h, Finset.sum_const_zero]
    have hc1 : cmass P rnk W x y = 1 := le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    have hR0 : ∑ z, Rres P rnk W x y z = 0 := by rw [Rres_sum P rnk W hPmass, hc1]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Rres_nonneg P rnk W hPnn x y z)).mp hR0
    exact (this b (Finset.mem_univ b)).symm

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

include hPnn hPmass in
/-- **Right marginal invariant:** `ρ_t + (U_t's right marginal) = t`-step law from `j`. -/
lemma right_marginal (t : ℕ) (z : α) :
    rhovec P rnk W i j t z + ∑ x, Umat P rnk W i j t x z = Mpow P t j z := by
  induction t generalizing z with
  | zero =>
    simp only [rhovec, Umat, Mpow, zero_add]
    by_cases hz : z = j
    · subst hz; simp
    · rw [if_neg (fun h => hz h.symm)]
      apply Finset.sum_eq_zero
      intro x _
      exact if_neg (fun h => hz h.2)
  | succ t ih =>
    have hU : ∑ x, Umat P rnk W i j (t + 1) x z
        = ∑ x, ∑ y, Umat P rnk W i j t x y * Rres P rnk W x y z := by
      simp only [Umat]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← Finset.mul_sum, Kres_right_marginal P rnk W hPnn hPmass p q z]
    rw [show Mpow P (t + 1) j z = ∑ a, Mpow P t j a * P a z from rfl]
    simp only [rhovec]
    rw [hU, add_assoc]
    rw [show (∑ x, ∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z)
        + ∑ x, ∑ y, Umat P rnk W i j t x y * Rres P rnk W x y z
        = ∑ y, (∑ x, Umat P rnk W i j t x y) * P y z from ?_]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← add_mul, ih a]
    · rw [← Finset.sum_add_distrib]
      rw [show (∑ x, ((∑ y, Umat P rnk W i j t x y * Cpart P rnk W x y z)
          + ∑ y, Umat P rnk W i j t x y * Rres P rnk W x y z))
          = ∑ x, ∑ y, Umat P rnk W i j t x y * P y z from ?_]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_mul]
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← mul_add]
        congr 1
        unfold Rres; ring

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
lemma rho_le_left (t : ℕ) (z : α) : rhovec P rnk W i j t z ≤ Mpow P t i z := by
  have h := left_marginal P rnk W hPnn hPmass i j t z
  have h2 : 0 ≤ ∑ y, Umat P rnk W i j t z y :=
    Finset.sum_nonneg (fun y _ => Umat_nonneg P rnk W hPnn hPmass i j t z y)
  linarith

include hPnn hPmass in
lemma rho_le_right (t : ℕ) (z : α) : rhovec P rnk W i j t z ≤ Mpow P t j z := by
  have h := right_marginal P rnk W hPnn hPmass i j t z
  have h2 : 0 ≤ ∑ x, Umat P rnk W i j t x z :=
    Finset.sum_nonneg (fun x _ => Umat_nonneg P rnk W hPnn hPmass i j t x z)
  linarith

include hPnn hPmass in
lemma rho_mass_le_overlap (t : ℕ) :
    ∑ z, rhovec P rnk W i j t z ≤ overlap (Mpow P t i) (Mpow P t j) :=
  Finset.sum_le_sum (fun z _ => le_min (rho_le_left P rnk W hPnn hPmass i j t z)
    (rho_le_right P rnk W hPnn hPmass i j t z))

include hPnn hPmass in
lemma umass_eq (t : ℕ) : umass P rnk W i j t = 1 - ∑ z, rhovec P rnk W i j t z := by
  have hsum : ∑ z, (rhovec P rnk W i j t z + ∑ y, Umat P rnk W i j t z y) = ∑ z, Mpow P t i z :=
    Finset.sum_congr rfl (fun z _ => left_marginal P rnk W hPnn hPmass i j t z)
  rw [Finset.sum_add_distrib, Mpow_mass P hPmass t i] at hsum
  unfold umass
  linarith [hsum]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: harmonic values are controlled by overlap (route-independent bridge)

The convergence engine consumes a *minorization-driven* lower bound on the `m`-step overlap of two
killed-chain laws (produced by the windowed-coupling ITER).  This file supplies the missing half: a
bounded `m`-step-harmonic function `h` has its values at two starts pinned together by that overlap,
`|h i − h j| ≤ 2·B·(1 − overlap(pᵢ, pⱼ))`, where `pᵢ, pⱼ` are the two `m`-step laws.  This is pure
finite linear algebra (`∑(p−q)h ≤ B·‖p−q‖₁` plus the banked overlap/L¹ identity) and holds for *any*
convergence route — coupling, recurrence, or a direct renewal argument — so it can be banked now,
independent of how the overlap → 1 lower bound is eventually obtained.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Finset

variable {α : Type*} [Fintype α]

/-- **L¹ control of a weighted difference.** For probability vectors `p, q` on a finite type and a
bounded weight `h` (`|h z| ≤ B`), the difference of the two `h`-averages is bounded by `B` times the
`L¹` distance `∑ |p − q|`. -/
lemma weighted_diff_le_L1 {p q h : α → ℝ} {B : ℝ}
    (hB : ∀ z, |h z| ≤ B) :
    |∑ z, p z * h z - ∑ z, q z * h z| ≤ B * ∑ z, |p z - q z| := by
  have hrw : ∑ z, p z * h z - ∑ z, q z * h z = ∑ z, (p z - q z) * h z := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun z _ => ?_); ring
  rw [hrw]
  calc |∑ z, (p z - q z) * h z|
      ≤ ∑ z, |(p z - q z) * h z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, |p z - q z| * |h z| := by
        refine Finset.sum_congr rfl (fun z _ => ?_); rw [abs_mul]
    _ ≤ ∑ z, |p z - q z| * B := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        exact mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
    _ = B * ∑ z, |p z - q z| := by rw [← Finset.sum_mul, mul_comm]

/-- **Harmonic values pinned by overlap.** If `h` is bounded by `B` and equals its average against
two probability vectors `p, q` (the two `m`-step killed-chain laws from starts `i, j`), then the two
harmonic values differ by at most `2·B·(1 − overlap p q)`.  As the windowed coupling drives
`overlap p q → 1`, the harmonic values coalesce. -/
theorem harmonic_diff_le_overlap {p q h : α → ℝ} {hi hj B : ℝ}
    (hp : ∑ z, p z = 1) (hq : ∑ z, q z = 1)
    (hB : ∀ z, |h z| ≤ B)
    (hhi : hi = ∑ z, p z * h z) (hhj : hj = ∑ z, q z * h z) :
    |hi - hj| ≤ 2 * B * (1 - overlap p q) := by
  have hL1 : ∑ z, |p z - q z| = 2 * (1 - overlap p q) := by
    have hmin : ∀ z, min (p z) (q z) = (p z + q z - |p z - q z|) / 2 := by
      intro z
      rcases le_total (p z) (q z) with hle | hle
      · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring
    have hov : overlap p q = 1 - (1 / 2) * ∑ z, |p z - q z| := by
      unfold overlap
      rw [Finset.sum_congr rfl (fun z _ => hmin z), ← Finset.sum_div, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hp, hq]
      ring
    rw [hov]; ring
  rw [hhi, hhj]
  calc |∑ z, p z * h z - ∑ z, q z * h z|
      ≤ B * ∑ z, |p z - q z| := weighted_diff_le_L1 hB
    _ = B * (2 * (1 - overlap p q)) := by rw [hL1]
    _ = 2 * B * (1 - overlap p q) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Active coupling inequality (TASK #9 layer B, abstract core)

The route-independent coupling bound for the windowed pair coupling: if `h` is a bounded function on a
finite state type `α` that equals its `m`-step `Mpow`-average at two starts `i, j` (i.e. `h` is
`Mpow`-harmonic at those starts), then

  `|h i_val − h j_val| ≤ umass(i, j, m) · (2 B)`,

where `umass` is the unmatched (non-coalesced) pair mass of the windowed coupling and `2 B` plays the
role of the oscillation constant `osc(h)` (a FIXED finite constant once `h` is bounded — no `u`
oscillation bootstrap is needed).  This is the abstract content behind the spec's

  `|hitVal_J(i) − hitVal_J(j)| ≤ umass_active(i, j) · osc_J(u)`.

Proof: combine `harmonic_diff_le_overlap` (`|hi − hj| ≤ 2 B (1 − overlap p q)`) with the banked coupling
invariants `umass_eq` (`umass = 1 − ∑ ρ`) and `rho_mass_le_overlap` (`∑ ρ ≤ overlap`), giving
`1 − overlap ≤ umass`.  Pure finite-sum linear algebra.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
/-- `1 − overlap(Mpow m i, Mpow m j) ≤ umass(i, j, m)`: the un-shared mass of the two `m`-step laws is
controlled by the unmatched coupling mass. -/
lemma one_sub_overlap_le_umass (i j : α) (m : ℕ) :
    1 - overlap (Mpow P m i) (Mpow P m j) ≤ umass P rnk W i j m := by
  have hov : ∑ z, rhovec P rnk W i j m z ≤ overlap (Mpow P m i) (Mpow P m j) :=
    rho_mass_le_overlap P rnk W hPnn hPmass i j m
  have heq : umass P rnk W i j m = 1 - ∑ z, rhovec P rnk W i j m z :=
    umass_eq P rnk W hPnn hPmass i j m
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
include hPnn hPmass in
theorem solution (h : α → ℝ) (B : ℝ) (hB : ∀ z, |h z| ≤ B)
    (hi hj : ℝ) (i j : α) (m : ℕ)
    (hhi : hi = ∑ z, Mpow P m i z * h z) (hhj : hj = ∑ z, Mpow P m j z * h z) :
    |hi - hj| ≤ umass P rnk W i j m * (2 * B) := by
  have hp : ∑ z, Mpow P m i z = 1 := Mpow_mass P hPmass m i
  have hq : ∑ z, Mpow P m j z = 1 := Mpow_mass P hPmass m j
  have hov := harmonic_diff_le_overlap (p := Mpow P m i) (q := Mpow P m j)
    (h := h) (hi := hi) (hj := hj) (B := B) hp hq hB hhi hhj
  -- `|hi − hj| ≤ 2 B (1 − overlap) ≤ 2 B · umass`
  have hone := one_sub_overlap_le_umass P rnk W hPnn hPmass i j m
  -- B ≥ 0 from |h z| ≤ B
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB i)
  have h2B0 : 0 ≤ 2 * B := by linarith
  calc |hi - hj| ≤ 2 * B * (1 - overlap (Mpow P m i) (Mpow P m j)) := hov
    _ ≤ 2 * B * umass P rnk W i j m :=
        mul_le_mul_of_nonneg_left hone h2B0
    _ = umass P rnk W i j m * (2 * B) := by ring
