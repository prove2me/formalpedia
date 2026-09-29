-- Prove2me | solution 1 for mme_profiled_CW_permuted_source_product_restrict_power
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:27:28.826462+00:00
-- url     : https://prove2.me/submissions/c65ef880-b6e0-43b2-ba4f-feb24af08cd4

import Theorems.Thm_mme_profiled_CW_six_source_product_restrict_power
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso
import Theorems.Thm_mme_kronFin_mono_restrict
import Definitions.Def_mme_cyclicSymmetrization_public_perm

open MME MME.TensorObj
open scoped BigOperators
universe u

private theorem six_product {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) :
    Isomorphic (kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]

/-- Whole-owner mode permutations preserve the transfer of six source families
to elementary CW powers, including their exact input multiplicity. -/
theorem solution
    {K : Type u} [Field K] (N : ℕ) (inputs : Fin 6 → ℕ)
    (P : Fin 6 → ProfiledCW.Predicate (4 * N))
    (sigma : Fin 6 → Equiv.Perm (Fin 3)) :
    Restrict
      (sixSymmetrization (kronFin 6 (fun owner => permObj (sigma owner)
        (bigAdd (fun _ : Fin (inputs owner) => ProfiledCW.tensor K (P owner))))))
      (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
        (CWObj K 5).kronPow (144 * N))) := by
  apply (six_product _).2.trans
  apply (mme_kronFin_mono_restrict (fun owner =>
    (mme_sixSymmetrization_mode_permutation_iso
      (bigAdd (fun _ : Fin (inputs owner) => ProfiledCW.tensor K (P owner)))
      (sigma owner)).1)).trans
  exact mme_profiled_CW_six_source_product_restrict_power N inputs P


#print axioms solution
