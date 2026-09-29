-- Prove2me | solution 1 for mme_batched_restrictions_compose
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T14:47:17.792013+00:00
-- url     : https://prove2.me/submissions/4c49e1ab-835b-4b9f-8d08-3d885bbea0dc

import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested

open MME MME.TensorObj BigOperators
universe u
set_option autoImplicit false

private theorem swap_sums {K : Type u} [Field K] {a b : ℕ}
    (X : Fin a → Fin b → TensorObj K 3) :
    Isomorphic (bigAdd (fun i ↦ bigAdd (X i)))
      (bigAdd (fun j ↦ bigAdd (fun i ↦ X i j))) := by
  apply TensorQ.toQ_eq_iff.mp
  simp_rw [TensorQ.toQ_bigAdd]
  exact Finset.sum_comm

theorem solution {K : Type u} [Field K] (A B C : TensorObj K 3)
    (r s c d : ℕ)
    (hAB : Restrict (bigAdd (fun _ : Fin c ↦ B)) (bigAdd (fun _ : Fin r ↦ A)))
    (hBC : Restrict (bigAdd (fun _ : Fin d ↦ C)) (bigAdd (fun _ : Fin s ↦ B))) :
    Restrict (bigAdd (fun _ : Fin (c * d) ↦ C))
      (bigAdd (fun _ : Fin (r * s) ↦ A)) := by
  have hstart := (mme_bigAdd_fin_mul_isomorphic_nested
    (fun (_ : Fin c) (_ : Fin d) ↦ C)).1
  have hfinish := (mme_bigAdd_fin_mul_isomorphic_nested
    (fun (_ : Fin r) (_ : Fin s) ↦ A)).2
  exact hstart.trans ((mme_bigAdd_mono_restrict (fun _ : Fin c ↦ hBC)).trans
    ((swap_sums (fun (_ : Fin c) (_ : Fin s) ↦ B)).1.trans
      ((mme_bigAdd_mono_restrict (fun _ : Fin s ↦ hAB)).trans
        ((swap_sums (fun (_ : Fin s) (_ : Fin r) ↦ A)).1.trans hfinish))))
