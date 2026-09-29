-- Prove2me | solution 1 for mme_type_cover_uniform_copy_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T14:47:22.223048+00:00
-- url     : https://prove2.me/submissions/d1aec219-d696-44ef-8af1-12d1b302457a

import Theorems.Thm_mme_bigAdd_mono_restrict
import Definitions.Def_mme_rank_bridge

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

theorem solution {K : Type u} [Field K] {types copies : ℕ}
    (source target : TensorObj K 3) (piece : Fin types → TensorObj K 3)
    (hcover : Restrict target (bigAdd piece))
    (hextract : ∀ j, Restrict (bigAdd (fun _ : Fin copies ↦ piece j)) source) :
    Restrict (bigAdd (fun _ : Fin copies ↦ target))
      (bigAdd (fun _ : Fin types ↦ source)) := by
  exact (mme_bigAdd_mono_restrict (fun _ : Fin copies ↦ hcover)).trans
    ((swap_sums (fun (_ : Fin copies) (j : Fin types) ↦ piece j)).1.trans
      (mme_bigAdd_mono_restrict hextract))
