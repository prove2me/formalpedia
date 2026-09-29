-- Prove2me | solution 1 for TropicalLA.tmul_const_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:52:53.807179+00:00
-- url     : https://prove2.me/submissions/43470043-4323-4db0-b6a1-db601c62600b

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (X A : Matrix ι ι ℝ) (c : ℝ) :
    tmul (fun i j => c + X i j) A = fun i j => c + tmul X A i j := by
  funext i j
  simp only [tmul]
  -- adding a constant commutes with taking a maximum
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun k hk => ?_
    have := Finset.le_sup' (fun k => X i k + A k j) hk
    simp only at this ⊢
    linarith
  · obtain ⟨k, hk, hkmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k => X i k + A k j)
    rw [hkmax]
    have := Finset.le_sup' (fun k => c + X i k + A k j) hk
    simp only at this ⊢
    linarith
