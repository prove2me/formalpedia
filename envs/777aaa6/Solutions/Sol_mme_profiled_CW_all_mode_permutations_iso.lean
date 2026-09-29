-- Prove2me | solution 1 for mme_profiled_CW_all_mode_permutations_iso
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:23:25.722248+00:00
-- url     : https://prove2.me/submissions/de22192f-5ef4-47c5-abca-d90ca8a74277

import Theorems.Thm_mme_profiled_CW_mode_permutation_iso

open MME MME.TensorObj MME.ProfiledCW PiTensorProduct
universe u

private theorem perm_trans_eq {K : Type u} [Field K]
    (e f : Equiv.Perm (Fin 3)) (T : TensorObj K 3) :
    permObj f (permObj e T) = permObj (e.trans f) T := by
  unfold permObj
  congr 1
  exact reindex_reindex e f T.t

private theorem perm_refl_eq {K : Type u} [Field K] (T : TensorObj K 3) :
    permObj (Equiv.refl _) T = T := by
  cases T
  simp only [permObj, reindex_refl]
  rfl

private theorem compose_profile_permutations {K : Type u} [Field K] {N : ℕ}
    (e f : Equiv.Perm (Fin 3))
    (he : ∀ P : Predicate N,
      Isomorphic (tensor K (fun i => P (e.symm i))) (permObj e (tensor K P)))
    (hf : ∀ P : Predicate N,
      Isomorphic (tensor K (fun i => P (f.symm i))) (permObj f (tensor K P)))
    (P : Predicate N) :
    Isomorphic (tensor K (fun i => P ((e.trans f).symm i)))
      (permObj (e.trans f) (tensor K P)) := by
  have h := (hf (fun i => P (e.symm i))).trans (permObj_isomorphic f (he P))
  simpa only [perm_trans_eq] using h

/-- Every mode permutation preserves a CW5 profile projection, after the
profile predicates are transported by the same permutation. -/
theorem solution {K : Type u} [Field K] {N : ℕ}
    (P : Predicate N) (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic (tensor K (fun i => P (sigma.symm i)))
      (permObj sigma (tensor K P)) := by
  have hc := fun P : Predicate N =>
    mme_profiled_CW_mode_permutation_iso (K := K) P cyclicPerm (Or.inl rfl)
  have hs := fun P : Predicate N =>
    mme_profiled_CW_mode_permutation_iso (K := K) P swapFirstTwoPerm (Or.inr rfl)
  have hcc := compose_profile_permutations cyclicPerm cyclicPerm hc hc
  have hsc := compose_profile_permutations swapFirstTwoPerm cyclicPerm hs hc
  have hscc := compose_profile_permutations swapFirstTwoPerm
    (cyclicPerm.trans cyclicPerm) hs hcc
  have cases_perm : ∀ e : Equiv.Perm (Fin 3),
      e = Equiv.refl _ ∨ e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm ∨
      e = swapFirstTwoPerm ∨ e = swapFirstTwoPerm.trans cyclicPerm ∨
      e = swapFirstTwoPerm.trans (cyclicPerm.trans cyclicPerm) := by decide
  rcases cases_perm sigma with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Equiv.refl_symm, Equiv.refl_apply, perm_refl_eq] using
      (Isomorphic.refl (tensor K P))
  · exact hc P
  · exact hcc P
  · exact hs P
  · exact hsc P
  · exact hscc P


#print axioms solution
