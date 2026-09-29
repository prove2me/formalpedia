-- Prove2me | solution 1 for mme_profiled_CW_repeated_six_restrict_power
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:46:38.038986+00:00
-- url     : https://prove2.me/submissions/a0f42d62-a14c-495a-ae07-a1e51d9640d8

import Theorems.Thm_mme_profiled_CW_tensor_restrict_power
import Theorems.Thm_mme_CW_six_symmetrized_power_four_mul_isomorphic
import Theorems.Thm_mme_sixSymmetrization_repeated_isomorphic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME MME.TensorObj
universe u
set_option autoImplicit false

/-- Repeated profiled sources give the sixth power of their input multiplicity
and twenty-four elementary CW factors per block after symmetrization. -/
theorem solution
    {K : Type u} [Field K] (N inputs : ℕ) (P : ProfiledCW.Predicate (4 * N)) :
    Restrict
      (sixSymmetrization (bigAdd (fun _ : Fin inputs => ProfiledCW.tensor K P)))
      (bigAdd (fun _ : Fin (inputs ^ 6) => (CWObj K 5).kronPow (24 * N))) := by
  have hproject := mme_bigAdd_mono_restrict
    (fun _ : Fin inputs => mme_profiled_CW_tensor_restrict_power (K := K) P)
  exact (mme_sixSymmetrization_restrict hproject).trans
    ((mme_sixSymmetrization_repeated_isomorphic inputs
      ((CWObj K 5).kronPow (4 * N))).2.trans
      (mme_bigAdd_mono_restrict (fun _ : Fin (inputs ^ 6) =>
        (mme_CW_six_symmetrized_power_four_mul_isomorphic (K := K) 5 N).1)))


#print axioms solution
