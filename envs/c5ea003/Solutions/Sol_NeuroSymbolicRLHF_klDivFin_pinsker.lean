-- Prove2me | solution 1 for NeuroSymbolicRLHF.klDivFin_pinsker
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T07:31:48.650099+00:00
-- url     : https://prove2.me/submissions/0d35e78b-32fe-4c86-8ce0-5b11dd46da33

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFPinsker

open Finset Real BigOperators Set
open NeuroSymbolicRLHF

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Pointwise convexity estimate `a - b ≤ a log (a/b)` for `a ≥ 0 < b`. -/
private theorem term_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases eq_or_lt_of_le ha with h | h
  · simp [← h, hb.le]
  · have ht : 0 < b / a := div_pos hb h
    have := Real.log_le_sub_one_of_pos ht
    have hlog : Real.log (b / a) = -Real.log (a / b) := by
      rw [← Real.log_inv]; congr 1; field_simp
    rw [hlog] at this
    have : a * (-Real.log (a / b)) ≤ a * (b / a - 1) := by
      exact mul_le_mul_of_nonneg_left this ha
    have hfield : a * (b / a - 1) = b - a := by field_simp
    nlinarith [this]

/-- Gibbs' inequality: KL is nonnegative. -/
private theorem klDivFin_nonneg {p q : ι → ℝ} (hp : IsProb p) (hq : IsPosProb q) :
    0 ≤ klDivFin p q := by
  have key : ∑ i, (p i - q i) ≤ ∑ i, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum (fun i _ => term_le (p i) (q i) (hp.nonneg i) (hq.pos i))
  have hz : ∑ i : ι, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp.sum_one, hq.sum_one, sub_self]
  rw [hz] at key
  exact key

private theorem hasDerivAt_pinskerH {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerH (pinskerG x) x := by
  have h2 : x + 2 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log x + 1) x :=
    hasDerivAt_mul_log hx.ne'
  have hid : HasDerivAt (fun y : ℝ => (5/2 : ℝ) * y) (5/2) x := by
    simpa using (hasDerivAt_id x).const_mul (5/2 : ℝ)
  have h4 : HasDerivAt (fun y : ℝ => (y+2)⁻¹) (-(1)/(x+2)^2) x :=
    ((hasDerivAt_id x).add_const 2).inv h2
  have h6 : HasDerivAt (fun y : ℝ => (27/2 : ℝ) * (y+2)⁻¹) ((27/2) * (-(1)/(x+2)^2)) x :=
    h4.const_mul (27/2 : ℝ)
  have h5 : HasDerivAt pinskerH (Real.log x + 1 - 5/2 + 7 * 0 - (27/2) * (-(1)/(x+2)^2)) x := by
    have := ((h1.sub hid).add_const 7).sub h6
    simpa [pinskerH] using this
  convert h5 using 1
  unfold pinskerG
  field_simp
  ring

private theorem hasDerivAt_pinskerG {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerG (1/x - 27/(x+2)^3) x := by
  have h2 : x + 2 ≠ 0 := by linarith
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun y : ℝ => (y+2)^2) (2*(x+2)) x := by
    have := ((hasDerivAt_id x).add_const 2).pow 2
    simpa using this
  have h4 : HasDerivAt (fun y : ℝ => ((y+2)^2)⁻¹) (-(2*(x+2))/((x+2)^2)^2) x :=
    h3.inv (by positivity)
  have h6 : HasDerivAt (fun y : ℝ => (27/2 : ℝ) * ((y+2)^2)⁻¹)
      ((27/2) * (-(2*(x+2))/((x+2)^2)^2)) x := h4.const_mul (27/2 : ℝ)
  have h5 : HasDerivAt pinskerG (x⁻¹ + 0 - 0 + (27/2) * (-(2*(x+2))/((x+2)^2)^2)) x := by
    have := ((h1.add_const 1).sub_const (5/2 : ℝ)).add h6
    simpa [pinskerG] using this
  convert h5 using 1
  field_simp
  ring

private theorem pinskerG_one : pinskerG 1 = 0 := by
  unfold pinskerG
  norm_num

private theorem pinskerH_one : pinskerH 1 = 0 := by
  unfold pinskerH
  norm_num

private theorem pinskerG_deriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ 1/x - 27/(x+2)^3 := by
  have h2 : (0:ℝ) < x + 2 := by linarith
  have hkey : 27 * x ≤ (x+2)^3 := by nlinarith [sq_nonneg (x - 1), hx.le]
  rw [sub_nonneg, div_le_div_iff₀ (by positivity : (0:ℝ) < (x+2)^3) hx]
  nlinarith [hkey]

private theorem pinskerG_monotone : MonotoneOn pinskerG (Ioi (0:ℝ)) := by
  have hconv : Convex ℝ (Ioi (0:ℝ)) := convex_Ioi 0
  refine monotoneOn_of_deriv_nonneg hconv ?_ ?_ ?_
  · intro x hx
    exact ((hasDerivAt_pinskerG (mem_Ioi.1 hx)).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact ((hasDerivAt_pinskerG (mem_Ioi.1 hx)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := mem_Ioi.1 hx
    rw [(hasDerivAt_pinskerG hx0).deriv]
    exact pinskerG_deriv_nonneg hx0

private theorem pinskerH_nonneg_of_pos {x : ℝ} (hx : 0 < x) : 0 ≤ pinskerH x := by
  rcases le_total 1 x with h1 | h1
  · have hmono : MonotoneOn pinskerH (Ici (1:ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
      · intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le one_pos (mem_Ici.1 hy)
        exact ((hasDerivAt_pinskerH hy0).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy0 : 0 < y := lt_trans one_pos (mem_Ioi.1 hy)
        exact ((hasDerivAt_pinskerH hy0).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy1 : (1:ℝ) < y := mem_Ioi.1 hy
        have hy0 : 0 < y := lt_trans one_pos hy1
        rw [(hasDerivAt_pinskerH hy0).deriv]
        have := pinskerG_monotone (mem_Ioi.2 one_pos) (mem_Ioi.2 hy0) hy1.le
        rw [pinskerG_one] at this
        exact this
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 h1) h1
    rwa [pinskerH_one] at this
  · have hanti : AntitoneOn pinskerH (Ioc (0:ℝ) 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
      · intro y hy
        exact ((hasDerivAt_pinskerH (mem_Ioc.1 hy).1).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        exact ((hasDerivAt_pinskerH (mem_Ioo.1 hy).1).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        obtain ⟨hy0, hy1⟩ := mem_Ioo.1 hy
        rw [(hasDerivAt_pinskerH hy0).deriv]
        have := pinskerG_monotone (mem_Ioi.2 hy0) (mem_Ioi.2 one_pos) hy1.le
        rw [pinskerG_one] at this
        exact this
    have := hanti (mem_Ioc.2 ⟨hx, h1⟩) (mem_Ioc.2 ⟨one_pos, le_rfl⟩) h1
    rwa [pinskerH_one] at this

private theorem xlogx_sub_ge {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1)^2 / (2 * (x + 2)) ≤ x * Real.log x - x + 1 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    norm_num
  · have hH := pinskerH_nonneg_of_pos h
    have h2 : x + 2 ≠ 0 := by linarith
    have hrw : x * Real.log x - x + 1 - 3 * (x - 1)^2 / (2 * (x + 2)) = pinskerH x := by
      unfold pinskerH
      field_simp
      ring
    linarith [hrw ▸ hH]

private theorem kl_term_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    3 * (a - b)^2 / (2 * (a + 2*b)) ≤ a * Real.log (a / b) - a + b := by
  have hx := xlogx_sub_ge (x := a / b) (div_nonneg ha hb.le)
  have hmul := mul_le_mul_of_nonneg_left hx hb.le
  have hlhs : b * (3 * (a/b - 1)^2 / (2 * (a/b + 2))) = 3 * (a - b)^2 / (2 * (a + 2*b)) := by
    have hden : a + 2*b ≠ 0 := by positivity
    field_simp
  have hrhs : b * ((a/b) * Real.log (a/b) - a/b + 1) = a * Real.log (a/b) - a + b := by
    field_simp
  rw [hlhs, hrhs] at hmul
  exact hmul

theorem solution {p q : ι → ℝ} (hp : IsProb p) (hq : IsPosProb q) :
    (∑ i, |p i - q i|)^2 ≤ 2 * klDivFin p q := by
  set w : ι → ℝ := fun i => p i + 2 * q i with hw
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have := hp.nonneg i
    have := hq.pos i
    simp only [hw]
    linarith
  have hwsum : ∑ i, w i = 3 := by
    simp only [hw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.sum_one, hq.sum_one]
    norm_num
  have hterm : ∀ i : ι, 3 * (p i - q i)^2 / (2 * w i)
      ≤ p i * Real.log (p i / q i) - p i + q i := fun i => kl_term_ge (hp.nonneg i) (hq.pos i)
  have hsum : ∑ i, 3 * (p i - q i)^2 / (2 * w i) ≤ klDivFin p q := by
    have h1 : ∑ i, (p i * Real.log (p i / q i) - p i + q i) = klDivFin p q := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.sum_one, hq.sum_one]
      simp [klDivFin]
    calc ∑ i, 3 * (p i - q i)^2 / (2 * w i)
        ≤ ∑ i, (p i * Real.log (p i / q i) - p i + q i) := Finset.sum_le_sum fun i _ => hterm i
      _ = klDivFin p q := h1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun i => |p i - q i| / Real.sqrt (w i)) (fun i => Real.sqrt (w i))
  have hprod : ∀ i : ι, (|p i - q i| / Real.sqrt (w i)) * Real.sqrt (w i) = |p i - q i| := by
    intro i
    have : Real.sqrt (w i) ≠ 0 := by
      have := Real.sqrt_pos.2 (hwpos i)
      exact ne_of_gt this
    field_simp
  have hsq1 : ∀ i : ι, (|p i - q i| / Real.sqrt (w i))^2 = (p i - q i)^2 / w i := by
    intro i
    rw [div_pow, Real.sq_sqrt (hwpos i).le, sq_abs]
  have hsq2 : ∀ i : ι, (Real.sqrt (w i))^2 = w i := fun i => Real.sq_sqrt (hwpos i).le
  rw [Finset.sum_congr rfl (fun i _ => hprod i), Finset.sum_congr rfl (fun i _ => hsq1 i),
    Finset.sum_congr rfl (fun i _ => hsq2 i), hwsum] at hcs
  have hfrac : ∑ i, (p i - q i)^2 / w i ≤ (2/3) * klDivFin p q := by
    have h3 : ∑ i, 3 * (p i - q i)^2 / (2 * w i) = (3/2) * ∑ i, (p i - q i)^2 / w i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [h3] at hsum
    linarith
  nlinarith [hcs, hfrac, klDivFin_nonneg hp hq]
