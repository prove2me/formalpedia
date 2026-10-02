-- Prove2me | solution 1 for BookSixth.log_sum_inequality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T07:25:48.923166+00:00
-- url     : https://prove2.me/submissions/a5da586b-f15c-46fe-864f-afc2ef538428

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (ι : Type*) [Fintype ι] [Nonempty ι] (a b : ι → ℝ)
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ i, 0 < b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i))
      ≤ ∑ i, a i * Real.log (a i / b i) := by
  classical
  set A : ℝ := ∑ i, a i with hAdef
  set B : ℝ := ∑ i, b i with hBdef
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  have hne : Finset.univ.Nonempty := ⟨i0, Finset.mem_univ i0⟩
  have hA : 0 < A := by
    rw [hAdef]
    exact Finset.sum_pos (fun i _ => hapos i) hne
  have hB : 0 < B := by
    rw [hBdef]
    exact Finset.sum_pos (fun i _ => hbpos i) hne
  have hAne : A ≠ 0 := ne_of_gt hA
  have hBne : B ≠ 0 := ne_of_gt hB
  -- normalized distributions and the ratio points
  set p : ι → ℝ := fun i => a i / A with hpdef
  set q : ι → ℝ := fun i => b i / B with hqdef
  set f : ι → ℝ := fun i => q i / p i with hfdef
  have hppos : ∀ i, 0 < p i := fun i => div_pos (hapos i) hA
  have hqpos : ∀ i, 0 < q i := fun i => div_pos (hbpos i) hB
  have hfpos : ∀ i, 0 < f i := fun i => div_pos (hqpos i) (hppos i)
  have hpsum : ∑ i, p i = 1 := by
    rw [hpdef]
    simp only
    rw [← Finset.sum_div, hAdef, div_self hAne]
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hJ := hconc.le_map_sum (t := Finset.univ) (w := p)
    (p := f) (fun i _ => le_of_lt (hppos i)) hpsum
    (fun i _ => Set.mem_Ioi.mpr (hfpos i))
  simp only [smul_eq_mul] at hJ
  -- the weighted average of the ratio points is 1
  have havg : ∑ i, p i * f i = 1 := by
    have e : ∀ i, p i * f i = q i := by
      intro i
      simp only [hpdef, hqdef, hfdef]
      exact mul_div_cancel₀ _ (ne_of_gt (div_pos (hapos i) hA))
    rw [Finset.sum_congr rfl (fun i _ => e i)]
    simp only [hqdef]
    rw [← Finset.sum_div, hBdef, div_self hBne]
  rw [havg, Real.log_one] at hJ
  -- convert back: goal difference equals -A times the Jensen sum
  have hconv : ∀ i, a i * Real.log (a i / b i) - a i * Real.log (A / B)
      = -A * (p i * Real.log (f i)) := by
    intro i
    have hai : a i ≠ 0 := ne_of_gt (hapos i)
    have hbi : b i ≠ 0 := ne_of_gt (hbpos i)
    have hpi : p i ≠ 0 := ne_of_gt (hppos i)
    have hfi : f i ≠ 0 := ne_of_gt (hfpos i)
    have hqi : q i ≠ 0 := ne_of_gt (hqpos i)
    simp only [hpdef, hqdef, hfdef]
    rw [Real.log_div (div_ne_zero hbi hBne) (div_ne_zero hai hAne),
      Real.log_div hbi hBne, Real.log_div hai hAne,
      Real.log_div hai hbi, Real.log_div hAne hBne]
    field_simp
    ring
  have hdecomp : ∑ i, (a i * Real.log (a i / b i) - a i * Real.log (A / B))
      = (∑ i, a i * Real.log (a i / b i)) - A * Real.log (A / B) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hAdef]
  have hneg : 0 ≤ -A * (∑ i, p i * Real.log (f i)) :=
    mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (le_of_lt hA)) hJ
  have hpull : (∑ i, p i * Real.log (f i)) * (-A)
      = ∑ i, (p i * Real.log (f i)) * (-A) := Finset.sum_mul _ _ _
  have hsum : ∑ i, (a i * Real.log (a i / b i) - a i * Real.log (A / B))
      = -A * (∑ i, p i * Real.log (f i)) := by
    have e : ∀ i, (a i * Real.log (a i / b i) - a i * Real.log (A / B))
        = (p i * Real.log (f i)) * (-A) := by
      intro i
      rw [hconv i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e i), ← hpull]
    ring
  linarith [hdecomp, hsum, hneg]
