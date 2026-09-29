-- Prove2me | solution 1 for Herbst.herbst_differential_inequality_integrate
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:21:57.717882+00:00
-- url     : https://prove2.me/submissions/8298185e-8fe6-4f35-9f32-adb9cda562fd

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
open Set Filter Topology

theorem solution
    (g g' : ℝ → ℝ) (m C lam : ℝ)
    (hlam : 0 ≤ lam)
    (hg_cont : ContinuousOn g (Set.Icc 0 lam))
    (hg0 : g 0 = m)
    (hg_deriv : ∀ x ∈ Set.Ico (0 : ℝ) lam, HasDerivWithinAt g (g' x) (Set.Ici x) x)
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) lam, g' x ≤ C) :
    g lam ≤ m + C * lam := by
  have hB : ∀ x, HasDerivAt (fun x => m + C * x) C x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => m + C * x) (0 + C * 1) x :=
      (hasDerivAt_const x m).add ((hasDerivAt_id x).const_mul C)
    simpa using h1
  have hBcont : ContinuousOn (fun x => m + C * x) (Icc 0 lam) := by fun_prop
  have key : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) lam → g x ≤ m + C * x := by
    refine image_le_of_deriv_right_le_deriv_boundary hg_cont hg_deriv ?_ hBcont
      (fun x _ => (hB x).hasDerivWithinAt) hbound
    simp [hg0]
  simpa using key (right_mem_Icc.mpr hlam)

