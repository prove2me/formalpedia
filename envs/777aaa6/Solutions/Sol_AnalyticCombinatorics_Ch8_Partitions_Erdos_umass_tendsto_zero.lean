-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:51:02.470964+00:00
-- url     : https://prove2.me/submissions/e9ebf201-58fe-46a3-913c-62d2e2f54489

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

/-- Unmatched mass on pairs inside the rank window. -/
def goodMass (t : ℕ) : ℝ := ∑ x, ∑ y, if GoodW rnk W x y then Umat P rnk W i j t x y else 0

/-- Unmatched mass on pairs outside the rank window. -/
def badMass (t : ℕ) : ℝ := umass P rnk W i j t - goodMass P rnk W i j t

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

include hPnn hPmass in
lemma umass_core (t : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    umass P rnk W i j (t + 1)
      ≤ (1 - δ) * umass P rnk W i j t + δ * badMass P rnk W i j t := by
  rw [umass_succ_eq P rnk W hPnn hPmass i j t]
  have hge : δ * goodMass P rnk W i j t
      ≤ ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
    unfold goodMass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun y _ => ?_)
    by_cases hg : GoodW rnk W x y
    · rw [if_pos hg, mul_comm]
      exact mul_le_mul_of_nonneg_left (hminor x y hg) (Umat_nonneg P rnk W hPnn hPmass i j t x y)
    · rw [if_neg hg, mul_zero]
      exact mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j t x y) (cmass_nonneg P rnk W hPnn x y)
  unfold badMass
  linarith [hge]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the window-occupation form of the ITER bound

The fixed-window single-epoch ITER bound `1 − (1−δ)^m − δ·∑(1−δ)^{m−t−1}b_t` is **insufficient** for the
Erdős constant `C = π/√6`: a one-pass coupling with a fixed window cannot beat the rank-difference walk's
spread (the self-consistency `2 ln v = c v`, `c ≈ ⅔C ≈ 0.855 > 2/e`, has no solution — confirmed
independently).  The fix is to use the *cumulative window occupation* rather than the single-pass bad
mass: telescoping `umass_core` gives

  `umass m ≤ 1 − δ · ∑_{t<m} goodMass t`,

where `goodMass t` is the unmatched mass *inside* the window at step `t`.  This captures the recurrence
gain — every time the rank-difference walk returns to the window it earns another `δ` of coalescence —
so the convergence reduces to the single occupation input `∑_{t<m} goodMass t → 1/δ` (the rank-difference
walk's window local-time → ∞ for high-rank starts).  This file banks the telescoping half.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- **Window-occupation bound.** Telescoping the one-step contraction `umass_core` (with
`badMass = umass − goodMass`) gives that the unmatched mass after `m` steps is at most `1` minus `δ`
times the *cumulative window occupation* `∑_{t<m} goodMass t`.  Unlike the single-pass ITER bound, this
credits every window-return, so it survives the Erdős constant: coalescence follows once the occupation
reaches `1/δ`. -/
theorem umass_le_one_sub_occupation (m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    umass P rnk W i j m ≤ 1 - δ * ∑ t ∈ Finset.range m, goodMass P rnk W i j t := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
    have hu0 : umass P rnk W i j 0 = 1 := by
      unfold umass
      have hx : ∀ x, ∑ y, Umat P rnk W i j 0 x y = if x = i then (1:ℝ) else 0 := by
        intro x; simp only [Umat]; by_cases hx : x = i <;> simp [hx]
      rw [Finset.sum_congr rfl (fun x _ => hx x),
        Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ)), if_pos (Finset.mem_univ i)]
    rw [hu0]
  | succ m ih =>
    have hc := umass_core P rnk W hPnn hPmass i j m δ hδ0 hminor
    have hbad : badMass P rnk W i j m
        = umass P rnk W i j m - goodMass P rnk W i j m := rfl
    have hstep : umass P rnk W i j (m + 1)
        ≤ umass P rnk W i j m - δ * goodMass P rnk W i j m := by
      rw [hbad] at hc; nlinarith [hc]
    rw [Finset.sum_range_succ, mul_add]
    linarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the D²-energy coalescence bridge

A direct energy argument on the *substochastic* unmatched mass `Umat` (no conditioned walk needed).
With `D` the pair-difference and `E t = ∑ Umat t · D²`, the per-row second-moment drift is `≥ c` off the
window (`c = v₀ − 2Rη > 0`) and `≥ −R²` on the window (trivially, next energy `≥ 0`, `D² ≤ R²`).
Telescoping with `E ≤ R²·umass ≤ R²`:

  `c · ∑_{t<M} umass t ≤ R² + (c + R²) · ∑_{t<M} goodMass t`.

Combined with `umass_le_one_sub_occupation` (`δ·∑goodMass ≤ 1`), `∑ umass` is bounded, so (umass
nonincreasing) `umass M ≤ K₀/M → 0`.  Deterministic finite-sum.  Opus-authored (energy identity ChatGPT R11).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

/-- D²-weighted unmatched mass. -/
def energy (D : α → α → ℝ) (t : ℕ) : ℝ :=
  ∑ a, ∑ b, Umat P rnk W i j t a b * (D a b) ^ 2

include hPnn hPmass in
/-- `umass` is `≤ 1` (it starts at `1` and is nonincreasing). -/
lemma umass_le_one (t : ℕ) : umass P rnk W i j t ≤ 1 := by
  have hmono : ∀ s, umass P rnk W i j (s + 1) ≤ umass P rnk W i j s := by
    intro s
    rw [umass_succ_eq P rnk W hPnn hPmass i j s]
    have : 0 ≤ ∑ x, ∑ y, Umat P rnk W i j s x y * cmass P rnk W x y :=
      Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
        mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j s x y) (cmass_nonneg P rnk W hPnn x y)))
    linarith
  have h0 : umass P rnk W i j 0 = 1 := by
    unfold umass
    have hx : ∀ x, ∑ y, Umat P rnk W i j 0 x y = if x = i then (1 : ℝ) else 0 := by
      intro x; simp only [Umat]; by_cases hx : x = i <;> simp [hx]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ)),
      if_pos (Finset.mem_univ i)]
  induction t with
  | zero => rw [h0]
  | succ t ih => exact le_trans (hmono t) ih

include hPnn hPmass in
/-- **Energy controls occupation.** -/
theorem energy_controls_goodMass (D : α → α → ℝ) (c R : ℝ)
    (hD : ∀ a b, (D a b) ^ 2 ≤ R ^ 2)
    (hrow_off : ∀ x y, ¬ GoodW rnk W x y →
        c ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2)
    (M : ℕ) :
    c * (∑ t ∈ Finset.range M, umass P rnk W i j t)
      ≤ R ^ 2 + (c + R ^ 2) * ∑ t ∈ Finset.range M, goodMass P rnk W i j t := by
  have hUnn : ∀ t a b, 0 ≤ Umat P rnk W i j t a b := Umat_nonneg P rnk W hPnn hPmass i j
  have hrowEnn : ∀ x y, 0 ≤ ∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2 := fun x y =>
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (Kres_nonneg P rnk W hPnn hPmass x y a b) (sq_nonneg _)))
  have hrow : ∀ x y, (if GoodW rnk W x y then -R ^ 2 else c)
      ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2 := by
    intro x y
    by_cases hg : GoodW rnk W x y
    · rw [if_pos hg]; nlinarith [hrowEnn x y, hD x y]
    · rw [if_neg hg]; exact hrow_off x y hg
  have hstep : ∀ t, c * umass P rnk W i j t - (c + R ^ 2) * goodMass P rnk W i j t
      ≤ energy P rnk W i j D (t + 1) - energy P rnk W i j D t := by
    intro t
    have hexp : energy P rnk W i j D (t + 1)
        = ∑ x, ∑ y, Umat P rnk W i j t x y
            * (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) := by
      unfold energy
      have e1 : (∑ a, ∑ b, Umat P rnk W i j (t + 1) a b * (D a b) ^ 2)
          = ∑ a, ∑ b, ∑ x, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        simp only [Umat, Finset.sum_mul]
      rw [e1]
      calc (∑ a, ∑ b, ∑ x, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2)
          = ∑ a, ∑ x, ∑ b, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
            refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_comm]
        _ = ∑ x, ∑ a, ∑ b, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by rw [Finset.sum_comm]
        _ = ∑ x, ∑ a, ∑ y, ∑ b,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ => ?_))
            rw [Finset.sum_comm]
        _ = ∑ x, ∑ y, ∑ a, ∑ b,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
            refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.sum_comm]
        _ = ∑ x, ∑ y, Umat P rnk W i j t x y
              * (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun b _ => by ring)
    have hdiff : (∑ x, ∑ y, Umat P rnk W i j t x y
          * (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2)) - energy P rnk W i j D t
        = ∑ x, ∑ y, Umat P rnk W i j t x y
            * ((∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2) := by
      unfold energy
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => by ring)
    have hge : (∑ x, ∑ y, Umat P rnk W i j t x y
          * (if GoodW rnk W x y then -R ^ 2 else c))
        ≤ ∑ x, ∑ y, Umat P rnk W i j t x y
            * ((∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hrow x y) (hUnn t x y)))
    have hval : (∑ x, ∑ y, Umat P rnk W i j t x y
          * (if GoodW rnk W x y then -R ^ 2 else c))
        = c * umass P rnk W i j t - (c + R ^ 2) * goodMass P rnk W i j t := by
      unfold umass goodMass
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hg : GoodW rnk W x y
      · rw [if_pos hg, if_pos hg]; ring
      · rw [if_neg hg, if_neg hg]; ring
    rw [hexp, hdiff, ← hval]; exact hge
  have htel : c * (∑ t ∈ Finset.range M, umass P rnk W i j t)
      - (c + R ^ 2) * (∑ t ∈ Finset.range M, goodMass P rnk W i j t)
      ≤ energy P rnk W i j D M - energy P rnk W i j D 0 := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
      linarith [ih, hstep M]
  have hE0 : 0 ≤ energy P rnk W i j D 0 :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (hUnn 0 a b) (sq_nonneg _)))
  have hEM : energy P rnk W i j D M ≤ R ^ 2 := by
    have h1 : energy P rnk W i j D M ≤ ∑ a, ∑ b, Umat P rnk W i j M a b * R ^ 2 := by
      unfold energy
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (hD a b) (hUnn M a b)))
    have h2 : (∑ a, ∑ b, Umat P rnk W i j M a b * R ^ 2) = umass P rnk W i j M * R ^ 2 := by
      unfold umass; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_mul]
    have h3 : umass P rnk W i j M ≤ 1 := umass_le_one P rnk W hPnn hPmass i j M
    rw [h2] at h1; nlinarith [h1, h3, sq_nonneg R]
  linarith [htel, hE0, hEM]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: the unmatched mass tends to zero

Combining the D²-energy occupation control (`energy_controls_goodMass`) with the window-occupation bound
(`umass_le_one_sub_occupation`, giving `δ·∑goodMass ≤ 1`) shows the cumulative unmatched mass
`∑_{t<M} umass t ≤ K₀` is bounded uniformly in `M`.  Since `umass` is nonincreasing, `M·umass M ≤
∑_{t<M} umass t ≤ K₀`, so `umass M ≤ K₀/M → 0`.  This is the coalescence conclusion: the two coupled
killed chains' overlap → 1.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- `umass` is antitone. -/
lemma umass_antitone : Antitone (umass P rnk W i j) := by
  refine antitone_nat_of_succ_le (fun s => ?_)
  rw [umass_succ_eq P rnk W hPnn hPmass i j s]
  have : 0 ≤ ∑ x, ∑ y, Umat P rnk W i j s x y * cmass P rnk W x y :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
      mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j s x y) (cmass_nonneg P rnk W hPnn x y)))
  linarith

include hPnn hPmass in
lemma umass_nonneg (t : ℕ) : 0 ≤ umass P rnk W i j t :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
    Umat_nonneg P rnk W hPnn hPmass i j t x y))

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset Filter Topology
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)
include hPnn hPmass in
theorem solution (D : α → α → ℝ) (c R δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hD : ∀ a b, (D a b) ^ 2 ≤ R ^ 2)
    (hrow_off : ∀ x y, ¬ GoodW rnk W x y →
        c ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    Tendsto (umass P rnk W i j) atTop (𝓝 0) := by
  set K0 := (R ^ 2 + (c + R ^ 2) / δ) / c with hK0
  -- δ·∑goodMass ≤ 1  (from brick 81 and umass ≥ 0)
  have hgm : ∀ M, δ * ∑ t ∈ Finset.range M, goodMass P rnk W i j t ≤ 1 := by
    intro M
    have h81 := umass_le_one_sub_occupation P rnk W hPnn hPmass i j M δ hδ.le hminor
    linarith [umass_nonneg P rnk W hPnn hPmass i j M, h81]
  -- ∑ umass ≤ K0
  have hcR : 0 ≤ c + R ^ 2 := by nlinarith [hc, sq_nonneg R]
  have hsum : ∀ M, ∑ t ∈ Finset.range M, umass P rnk W i j t ≤ K0 := by
    intro M
    have he := energy_controls_goodMass P rnk W hPnn hPmass i j D c R hD hrow_off M
    have hgmle : ∑ t ∈ Finset.range M, goodMass P rnk W i j t ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]; linarith [hgm M]
    have hg : (c + R ^ 2) * ∑ t ∈ Finset.range M, goodMass P rnk W i j t ≤ (c + R ^ 2) / δ := by
      rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left hgmle hcR
    have hcK0 : c * K0 = R ^ 2 + (c + R ^ 2) / δ := by
      rw [hK0]; field_simp
    have hKle : c * ∑ t ∈ Finset.range M, umass P rnk W i j t ≤ c * K0 := by
      rw [hcK0]; linarith [he, hg]
    exact le_of_mul_le_mul_left hKle hc
  -- M · umass M ≤ ∑ umass ≤ K0
  have hMu : ∀ M : ℕ, (M : ℝ) * umass P rnk W i j M ≤ K0 := by
    intro M
    have hge : (M : ℝ) * umass P rnk W i j M ≤ ∑ t ∈ Finset.range M, umass P rnk W i j t := by
      have hle : ∑ t ∈ Finset.range M, umass P rnk W i j M
          ≤ ∑ t ∈ Finset.range M, umass P rnk W i j t :=
        Finset.sum_le_sum (fun t ht =>
          umass_antitone P rnk W hPnn hPmass i j (le_of_lt (Finset.mem_range.1 ht)))
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    exact le_trans hge (hsum M)
  -- squeeze: 0 ≤ umass M ≤ K0/M → 0
  have hg0 : Tendsto (fun n : ℕ => K0 / (n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfg : ∀ᶠ M : ℕ in atTop, umass P rnk W i j M ≤ K0 / (M : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [le_div_iff₀ (by exact_mod_cast hM : (0 : ℝ) < (M : ℝ))]
    linarith [hMu M]
  exact squeeze_zero' (Eventually.of_forall (umass_nonneg P rnk W hPnn hPmass i j)) hfg hg0
