-- Prove2me | solution 1 for mme_exact_step_permuted_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:26:51.470737+00:00
-- url     : https://prove2.me/submissions/97b6b917-ff27-4d20-bfdf-e126af2140c0

import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_mono_restrict
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME MME.TensorObj MME.ProfiledCW
universe u

private theorem perm_repeated {K : Type u} [Field K]
    (sigma : Equiv.Perm (Fin 3)) (T : TensorObj K 3) (n : ℕ) :
    Isomorphic (permObj sigma (bigAdd (fun _ : Fin n => T)))
      (bigAdd (fun _ : Fin n => permObj sigma T)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [← TensorQ.permAut_toQ, TensorQ.toQ_bigAdd, map_sum, TensorQ.toQ_bigAdd]
  simp only [TensorQ.permAut_toQ]

/-- Exact hashing steps combine after independently permuting whole regions.
Every factor retains its own post-repair integer copy count. -/
theorem solution {K : Type u} [Field K]
    {n ell : ℕ} (N : Fin n → ℕ) (P : ∀ r, Predicate (N r))
    (E : ∀ r, ExactStep ell (N r) (P r)) (sigma : Fin n → Equiv.Perm (Fin 3)) :
    Restrict
      (kronFin n (fun r => bigAdd (fun _ : Fin (E r).copies =>
        tensor K (fun i => (E r).output ((sigma r).symm i)))))
      (kronFin n (fun r => tensor K (fun i => P r ((sigma r).symm i)))) := by
  apply mme_kronFin_mono_restrict
  intro r
  have h := permObj_restrict (sigma r) (mme_recursive_profiled_CW_exact_step (K := K) (E r))
  exact (mme_bigAdd_mono_restrict (fun _ : Fin (E r).copies =>
      (mme_profiled_CW_all_mode_permutations_iso (E r).output (sigma r)).1)).trans
    ((perm_repeated (sigma r) (tensor K (E r).output) (E r).copies).2.trans
      (h.trans (mme_profiled_CW_all_mode_permutations_iso (P r) (sigma r)).2))


#print axioms solution
