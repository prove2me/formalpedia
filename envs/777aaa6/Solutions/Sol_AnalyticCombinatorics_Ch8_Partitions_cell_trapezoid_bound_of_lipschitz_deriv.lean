-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.cell_trapezoid_bound_of_lipschitz_deriv
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:30:47.532881+00:00
-- url     : https://prove2.me/submissions/43af939c-8868-4464-99d9-981fe5cfce65

import Mathlib

namespace AnalyticCombinatorics end AnalyticCombinatorics
namespace AnalyticCombinatorics.Ch8 end AnalyticCombinatorics.Ch8
namespace AnalyticCombinatorics.Ch8.Partitions end AnalyticCombinatorics.Ch8.Partitions

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Per-cell trapezoid error from a Lipschitz derivative (HR constant, brick 2)

Producer for the `hcell` hypothesis of `TrapezoidEM.lean`'s summation core:
for `g` with derivative `gp` on `[0,2]` and `gp` `M`-Lipschitz there,
`|trapezoid avg - integral avg| ≤ M·h²` on every cell `[a,a+h] ⊆ [0,2]`.
(ChatGPT R4 chord-interpolation proof; non-sharp constant `M`, sufficient for the
summation brick.)
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- The chord through `(a,g a)` and `(a+h,g(a+h))`, in linear form. -/
private noncomputable def chord (g : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  ((g (a + h) - g a) / h) * x + (((a + h) * g a - a * g (a + h)) / h)

private lemma chord_eq_endpoint (g : ℝ → ℝ) {a h x : ℝ} (hh : h ≠ 0) :
    chord g a h x = ((a + h - x) / h) * g a + ((x - a) / h) * g (a + h) := by
  unfold chord; field_simp [hh]; ring

private lemma integral_chord (g : ℝ → ℝ) {a h : ℝ} (hh : h ≠ 0) :
    (∫ x in a..(a + h), chord g a h x) = h * ((g a + g (a + h)) / 2) := by
  unfold chord
  set A : ℝ := (g (a + h) - g a) / h with hA
  set B : ℝ := ((a + h) * g a - a * g (a + h)) / h with hB
  have hInt1 : IntervalIntegrable (fun x : ℝ => A * x) MeasureTheory.volume a (a + h) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun _x : ℝ => B) MeasureTheory.volume a (a + h) :=
    continuous_const.intervalIntegrable _ _
  change (∫ x in a..(a + h), A * x + B) = h * ((g a + g (a + h)) / 2)
  rw [intervalIntegral.integral_add hInt1 hInt2, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  rw [hA, hB]; simp only [smul_eq_mul]; field_simp [hh]; ring

/-- First-order Taylor error from a Lipschitz derivative, order-agnostic:
`|g y - g x - (y-x) gp x| ≤ M (y-x)²` for `x, y ∈ [0,2]` (any order). -/
private lemma first_order_error_bound_of_lipschitz_deriv
    {g gp : ℝ → ℝ} {M x y : ℝ} (hM : 0 ≤ M)
    (hxI : x ∈ Set.Icc (0 : ℝ) 2) (hyI : y ∈ Set.Icc (0 : ℝ) 2)
    (hderiv : ∀ z ∈ Set.Icc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Icc (0 : ℝ) 2, ∀ w ∈ Set.Icc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    |g y - g x - (y - x) * gp x| ≤ M * (y - x) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 2 := Set.uIcc_subset_Icc hxI hyI
  have hIntGp : IntervalIntegrable gp MeasureTheory.volume x y := hint_gp hxI.1 hyI.2
  have hIntConst : IntervalIntegrable (fun _z : ℝ => gp x) MeasureTheory.volume x y :=
    continuous_const.intervalIntegrable _ _
  have hIntDiff : IntervalIntegrable (fun z : ℝ => gp z - gp x) MeasureTheory.volume x y :=
    hIntGp.sub hIntConst
  have hderivF : ∀ z ∈ Set.uIcc x y,
      HasDerivAt (fun z : ℝ => g z - z * gp x) (gp z - gp x) z := by
    intro z hz
    have hg := hderiv z (hsub hz)
    have hlin : HasDerivAt (fun z : ℝ => z * gp x) (gp x) z := by
      simpa using (hasDerivAt_id z).mul_const (gp x)
    exact hg.sub hlin
  have hFTC : (∫ z in x..y, gp z - gp x) = (g y - y * gp x) - (g x - x * gp x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hIntDiff
  have herr_eq : g y - g x - (y - x) * gp x = ∫ z in x..y, gp z - gp x := by
    rw [hFTC]; ring
  have hnorm : ‖∫ z in x..y, gp z - gp x‖ ≤ (M * |y - x|) * |y - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro z hz
    have hzx : |z - x| ≤ |y - x| ∧ z ∈ Set.Icc (0 : ℝ) 2 := by
      rcases le_total x y with hle | hle
      · rw [Set.uIoc_of_le hle] at hz
        refine ⟨?_, le_trans hxI.1 (le_of_lt hz.1), le_trans hz.2 hyI.2⟩
        rw [abs_of_nonneg (by linarith [hz.1] : (0:ℝ) ≤ z - x),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]; linarith [hz.2]
      · rw [Set.uIoc_comm, Set.uIoc_of_le hle] at hz
        refine ⟨?_, le_trans hyI.1 (le_of_lt hz.1), le_trans hz.2 hxI.2⟩
        rw [abs_of_nonpos (by linarith [hz.2] : z - x ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]; linarith [hz.1]
    rw [Real.norm_eq_abs]
    calc |gp z - gp x| ≤ M * |z - x| := hlip z hzx.2 x hxI
      _ ≤ M * |y - x| := mul_le_mul_of_nonneg_left hzx.1 hM
  calc |g y - g x - (y - x) * gp x| = ‖∫ z in x..y, gp z - gp x‖ := by
        rw [herr_eq, Real.norm_eq_abs]
    _ ≤ (M * |y - x|) * |y - x| := hnorm
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring

/-- Pointwise chord interpolation error `|chord - g| ≤ M·h²` on the cell. -/
private lemma chord_error_bound_of_lipschitz_deriv
    {g gp : ℝ → ℝ} {M a h x : ℝ} (hM : 0 ≤ M)
    (hh : 0 < h) (ha : 0 ≤ a) (hb : a + h ≤ 2)
    (hderiv : ∀ z ∈ Set.Icc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Icc (0 : ℝ) 2, ∀ w ∈ Set.Icc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|)
    (hx : x ∈ Set.Icc a (a + h)) :
    |chord g a h x - g x| ≤ M * h ^ 2 := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ a + h := hx.2
  have hx0 : 0 ≤ x := le_trans ha hxa
  have hx2 : x ≤ 2 := le_trans hxb hb
  have hxI : x ∈ Set.Icc (0 : ℝ) 2 := ⟨hx0, hx2⟩
  have haI : a ∈ Set.Icc (0 : ℝ) 2 := ⟨ha, by linarith⟩
  have habI : a + h ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith, hb⟩
  have e1 : |g x - g a - (x - a) * gp x| ≤ M * (x - a) ^ 2 := by
    have hfo := first_order_error_bound_of_lipschitz_deriv (g := g) (gp := gp) (M := M)
      (x := x) (y := a) hM hxI haI hderiv hint_gp hlip
    rw [show g x - g a - (x - a) * gp x = -(g a - g x - (a - x) * gp x) by ring, abs_neg,
      show (x - a) ^ 2 = (a - x) ^ 2 by ring]
    exact hfo
  have e2 : |g (a + h) - g x - (a + h - x) * gp x| ≤ M * (a + h - x) ^ 2 :=
    first_order_error_bound_of_lipschitz_deriv (g := g) (gp := gp) (M := M) (x := x) (y := a + h)
      hM hxI habI hderiv hint_gp hlip
  have hα : 0 ≤ x - a := sub_nonneg.mpr hxa
  have hβ : 0 ≤ a + h - x := sub_nonneg.mpr hxb
  have hαh : 0 ≤ (x - a) / h := div_nonneg hα hh.le
  have hβh : 0 ≤ (a + h - x) / h := div_nonneg hβ hh.le
  have herr : g x - chord g a h x =
      ((a + h - x) / h) * (g x - g a - (x - a) * gp x)
        - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x) := by
    rw [chord_eq_endpoint g hh.ne']; field_simp [hh.ne']; ring
  have hterm1 : |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
        ≤ ((a + h - x) / h) * (M * (x - a) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hβh]; exact mul_le_mul_of_nonneg_left e1 hβh
  have hterm2 : |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
        ≤ ((x - a) / h) * (M * (a + h - x) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hαh]; exact mul_le_mul_of_nonneg_left e2 hαh
  have hmain : |g x - chord g a h x| ≤ M * (x - a) * (a + h - x) := by
    rw [herr]
    calc |((a + h - x) / h) * (g x - g a - (x - a) * gp x)
            - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
          ≤ |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
            + |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)| := abs_sub _ _
      _ ≤ ((a + h - x) / h) * (M * (x - a) ^ 2)
            + ((x - a) / h) * (M * (a + h - x) ^ 2) := add_le_add hterm1 hterm2
      _ = M * (x - a) * (a + h - x) := by field_simp [hh.ne']; ring
  rw [abs_sub_comm]
  calc |g x - chord g a h x| ≤ M * (x - a) * (a + h - x) := hmain
    _ ≤ M * h ^ 2 := by
        have hαle : x - a ≤ h := by linarith
        have hβle : a + h - x ≤ h := by linarith
        nlinarith [hM, hα, hβ, hαle, hβle]

end
end AnalyticCombinatorics.Ch8.Partitions

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions
open Filter Topology BigOperators
open scoped Topology BigOperators Interval
theorem solution
    {g gp : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ z ∈ Set.Icc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_g : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume u v)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Icc (0 : ℝ) 2, ∀ w ∈ Set.Icc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    ∀ ⦃a h : ℝ⦄, 0 < h → 0 ≤ a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2 := by
  intro a h hh ha hb
  have hIntG : IntervalIntegrable g MeasureTheory.volume a (a + h) := hint_g ha hb
  have hIntChord : IntervalIntegrable (fun x : ℝ => chord g a h x)
      MeasureTheory.volume a (a + h) := by
    unfold chord
    exact ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
  have hChordInt : (∫ x in a..(a + h), chord g a h x) = h * ((g a + g (a + h)) / 2) :=
    integral_chord g hh.ne'
  have hsubInt : (∫ x in a..(a + h), chord g a h x - g x)
      = (∫ x in a..(a + h), chord g a h x) - ∫ x in a..(a + h), g x :=
    intervalIntegral.integral_sub hIntChord hIntG
  have herr_eq : ((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x
      = (1 / h) * ∫ x in a..(a + h), chord g a h x - g x := by
    rw [hsubInt, hChordInt]; field_simp [hh.ne']
  have hpoint : ∀ x ∈ Set.uIoc a (a + h), ‖chord g a h x - g x‖ ≤ M * h ^ 2 := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc a (a + h) := by
      simpa [Set.uIoc_of_le (by linarith : a ≤ a + h)] using hx
    have hxIcc : x ∈ Set.Icc a (a + h) := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    rw [Real.norm_eq_abs]
    exact chord_error_bound_of_lipschitz_deriv (g := g) (gp := gp) (M := M)
      hM hh ha hb hderiv hint_gp hlip hxIcc
  have hnorm : ‖∫ x in a..(a + h), chord g a h x - g x‖ ≤ (M * h ^ 2) * |(a + h) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x|
        = |(1 / h) * ∫ x in a..(a + h), chord g a h x - g x| := by rw [herr_eq]
    _ = (1 / h) * ‖∫ x in a..(a + h), chord g a h x - g x‖ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hh), ← Real.norm_eq_abs]
    _ ≤ (1 / h) * ((M * h ^ 2) * |(a + h) - a|) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = M * h ^ 2 := by rw [show (a + h) - a = h by ring, abs_of_pos hh]; field_simp [hh.ne']
