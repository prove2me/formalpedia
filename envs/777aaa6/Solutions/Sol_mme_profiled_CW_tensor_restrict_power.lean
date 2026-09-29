-- Prove2me | solution 1 for mme_profiled_CW_tensor_restrict_power
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:18:02.821047+00:00
-- url     : https://prove2.me/submissions/4f4204a3-f186-4e2e-aed5-28c53f2e9980

import Definitions.Def_mme_recursive_profiled_CW_data

open MME
universe u
set_option autoImplicit false

/-- Every profiled CW tensor is an actual projection of the corresponding
power of the elementary CW tensor with parameter five. -/
theorem solution
    {K : Type u} [Field K] {N : ℕ} (P : ProfiledCW.Predicate N) :
    TensorObj.Restrict (ProfiledCW.tensor K P) ((CWObj K 5).kronPow N) := by
  let G := (ProfiledCW.raw K N).basisAllAllowedGrading (ProfiledCW.canonical K N)
    (fun i x => P i (ProfiledCW.fine x))
  exact ⟨fun i => G.blockProj i 0, rfl⟩


#print axioms solution
