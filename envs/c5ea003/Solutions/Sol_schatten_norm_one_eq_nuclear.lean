-- Prove2me | solution 1 for schatten_norm_one_eq_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T17:50:50.574142+00:00
-- url     : https://prove2.me/submissions/0a201405-1151-49b1-b155-879eef58c3f4

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
F4 — Schatten 1-norm equals the nuclear norm.
Source: Candès–Recht 2009 (arXiv:0805.4471), §6.1 lines 1633-1634.
-/

open Module LinearMap Matrix
open scoped BigOperators

namespace MatrixCompletion

variable {n1 n2 : ℕ}

theorem schatten_norm_one_eq_nuclear_proof (X : RealMatrix n1 n2) :
    schattenNorm 1 X = nuclearNorm X := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  unfold schattenNorm nuclearNorm
  have hrpow1 : ∀ a : ℝ, a.rpow 1 = a := fun a => Real.rpow_one a
  simp only [inv_one, hrpow1]
  set T := toEuclideanLin X
  rw [Finsupp.sum_of_support_subset T.singularValues
      (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
  · rw [Finset.sum_range fun k => T.singularValues k]
  · intro k hk
    rw [Finset.mem_range]
    by_contra hge
    push_neg at hge
    have hz : T.singularValues k = 0 := by
      apply T.singularValues_of_finrank_le; rw [hn]; exact hge
    rw [Finsupp.mem_support_iff] at hk
    exact hk hz

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

theorem solution (n1 n2 : Nat) (X : MatrixCompletion.RealMatrix n1 n2) :
    MatrixCompletion.schattenNorm 1 X = MatrixCompletion.nuclearNorm X :=
  MatrixCompletion.schatten_norm_one_eq_nuclear_proof X
