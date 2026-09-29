-- Prove2me | solution 1 for TropicalLA.tmulVec_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:50:45.754432+00:00
-- url     : https://prove2.me/submissions/1e19b87d-c161-4ddb-a642-9add40ecf9a2

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (A B : Matrix ι ι ℝ) (v : ι → ℝ) :
    tmulVec (tmul A B) v = tmulVec A (tmulVec B v) := by
  funext i
  simp only [tmulVec, tmul]
  -- both sides are `max_{k,j} (A i k + B k j + v j)`
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j _ => ?_
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k => A i k + B k j)
    rw [hkmax]
    have h1 := Finset.le_sup' (fun j' => B k j' + v j') (Finset.mem_univ j)
    have h2 := Finset.le_sup' (fun k' => A i k' + Finset.univ.sup' Finset.univ_nonempty
      (fun j' => B k' j' + v j')) hk
    simp only at h1 h2 ⊢
    linarith
  · refine Finset.sup'_le _ _ fun k _ => ?_
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => B k j + v j)
    rw [hjmax]
    have h1 := Finset.le_sup' (fun k' => A i k' + B k' j) (Finset.mem_univ k)
    have h2 := Finset.le_sup' (fun j' => Finset.univ.sup' Finset.univ_nonempty
      (fun k' => A i k' + B k' j') + v j') hj
    simp only at h1 h2 ⊢
    linarith
