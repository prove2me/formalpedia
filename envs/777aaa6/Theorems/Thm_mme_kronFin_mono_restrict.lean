-- Prove2me | Theorems.Thm_mme_kronFin_mono_restrict
-- name    : mme_kronFin_mono_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:58:50.848731+00:00
-- url     : https://prove2.me/theorems/a55a979d-8984-41bf-8ec2-509f30dce8f8
-- title:
--   Finite tensor products preserve restrictions
-- statement:
--   The tensor product of the factor mode maps combines independent restrictions, for any tensor order and including an empty family. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
open MME MME.TensorObj
universe u

theorem mme_kronFin_mono_restrict {K : Type u} [Field K] {d n : ℕ}
    {X Y : Fin n → TensorObj K d} (h : ∀ j, Restrict (X j) (Y j)) :
    Restrict (kronFin n X) (kronFin n Y) := by sorry
