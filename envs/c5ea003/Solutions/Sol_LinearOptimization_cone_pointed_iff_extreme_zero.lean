-- Prove2me | solution 1 for LinearOptimization.cone_pointed_iff_extreme_zero
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:18:26.782252+00:00
-- url     : https://prove2.me/submissions/db4aa91e-6bdb-4b80-88c8-f31ded8bbd31

import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Definitions.Def_LinearOptimization_RecessionCone
import Definitions.Def_ContainsLine
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence

open Matrix

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (LinearOptimization.IsPointedCone (LinearOptimization.polyhedron A 0) ↔
      ¬ LinearOptimization.ContainsLine (LinearOptimization.polyhedron A 0)) ∧
    (¬ LinearOptimization.ContainsLine (LinearOptimization.polyhedron A 0) ↔
      ∃ s : Finset (Fin m), s.card = n ∧
        LinearIndependent ℝ (fun i : s ↦ A i.1)) := by
  classical
  have hzero : (0 : Fin n → ℝ) ∈ LinearOptimization.polyhedron A 0 := by
    intro i
    simp [LinearOptimization.polyhedron]
  have ht := LinearOptimization.polyhedron_extreme_point_existence A 0 ⟨0, hzero⟩
  have hfirst :
      LinearOptimization.IsPointedCone (LinearOptimization.polyhedron A 0) ↔
        ¬ LinearOptimization.ContainsLine (LinearOptimization.polyhedron A 0) := by
    constructor
    · intro hpoint
      apply (ht.out 0 1).mp
      refine ⟨0, ?_⟩
      simpa [LinearOptimization.IsPointedCone] using hpoint
    · intro hnoline
      obtain ⟨y, hy⟩ := (ht.out 1 0).mp hnoline
      have hyzero : y = 0 := by
        have htwo : (2 : ℝ) • y ∈ LinearOptimization.polyhedron A 0 := by
          intro i
          have hyi : 0 ≤ A i ⬝ᵥ y := hy.1 i
          change 0 ≤ A i ⬝ᵥ ((2 : ℝ) • y)
          rw [dotProduct_smul, smul_eq_mul]
          exact mul_nonneg (by norm_num) hyi
        have hmid : y ∈ openSegment ℝ (0 : Fin n → ℝ) ((2 : ℝ) • y) := by
          refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
          ext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          ring
        exact (hy.2 hzero htwo hmid).symm
      subst y
      simpa [LinearOptimization.IsPointedCone] using hy
  exact ⟨hfirst, ht.out 1 2⟩
