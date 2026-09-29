-- Prove2me | solution 1 for mme_CW_q6_coupled_survivor_square_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:21:58.525754+00:00
-- url     : https://prove2.me/submissions/44744d4c-4827-499a-8f63-5f086f44e876

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_square_kronPow_iso
import Mathlib.Tactic

open MME
universe u
set_option autoImplicit false

/-- The coupled survivor has exactly the square matrix shape used in finite extraction. -/
theorem solution
    {K : Type u} [Field K] (L G : ℕ) :
    TensorObj.Isomorphic (coupledQ6Survivor K L G)
      (MMObj K (6 ^ (4 * G + 2 * L))
        (6 ^ (4 * G + 2 * L)) (6 ^ (4 * G + 2 * L))) := by
  have hhigh : TensorObj.Isomorphic (cyclicSymmetrization (MMObj K 6 1 6))
      (MMObj K 36 36 36) := by
    simpa using mme_MMObj_cyclicSymmetrization_iso (K := K) 6 1 6
  have hlow : TensorObj.Isomorphic (cyclicSymmetrization (MMObj K 1 6 1))
      (MMObj K 6 6 6) := by
    simpa using mme_MMObj_cyclicSymmetrization_iso (K := K) 1 6 1
  have pow_iso {X Y : TensorObj K 3} (h : TensorObj.Isomorphic X Y) (n : ℕ) :
      TensorObj.Isomorphic (X.kronPow n) (Y.kronPow n) := by
    apply TensorQ.toQ_eq_iff.mp
    simp only [TensorQ.toQ_kronPow, TensorQ.toQ_eq_iff.mpr h]
  have hh := (pow_iso hhigh (2 * G)).trans
    (mme_MMObj_square_kronPow_iso (K := K) 36 (2 * G))
  have hl := (pow_iso hlow (2 * L)).trans
    (mme_MMObj_square_kronPow_iso (K := K) 6 (2 * L))
  have h := (TensorQ.mul_respects_iso hh hl).trans
    (MMObj_kron_iso (K := K) (36 ^ (2 * G)) (36 ^ (2 * G)) (36 ^ (2 * G))
      (6 ^ (2 * L)) (6 ^ (2 * L)) (6 ^ (2 * L)))
  have hside : 36 ^ (2 * G) * 6 ^ (2 * L) = 6 ^ (4 * G + 2 * L) := by
    calc
      _ = (6 ^ 2) ^ (2 * G) * 6 ^ (2 * L) := by norm_num
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  simpa only [coupledQ6Survivor, hside] using h

#print axioms solution
