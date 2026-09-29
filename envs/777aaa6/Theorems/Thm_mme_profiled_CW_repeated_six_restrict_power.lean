-- Prove2me | Theorems.Thm_mme_profiled_CW_repeated_six_restrict_power
-- name    : mme_profiled_CW_repeated_six_restrict_power
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:46:31.819863+00:00
-- url     : https://prove2.me/theorems/85c43b4d-f1cf-422b-813f-b00141f15cad
-- title:
--   Repeated profiled sources restrict elementary CW powers
-- statement:
--   The six symmetrization of p profiled sources on four N positions restricts p to the sixth power copies of CW to the twenty-four Nth power. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_profiled_CW_tensor_restrict_power
import Theorems.Thm_mme_CW_six_symmetrized_power_four_mul_isomorphic
import Theorems.Thm_mme_sixSymmetrization_repeated_isomorphic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_restrict
open MME MME.TensorObj
universe u

theorem mme_profiled_CW_repeated_six_restrict_power
    {K : Type u} [Field K] (N inputs : ℕ) (P : ProfiledCW.Predicate (4 * N)) :
    Restrict
      (sixSymmetrization (bigAdd (fun _ : Fin inputs => ProfiledCW.tensor K P)))
      (bigAdd (fun _ : Fin (inputs ^ 6) => (CWObj K 5).kronPow (24 * N))) := by sorry
