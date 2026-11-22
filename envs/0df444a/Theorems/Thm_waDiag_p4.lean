-- Prove2me | Theorems.Thm_waDiag_p4
-- name    : waDiag.p4
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-22T19:28:32.346908+00:00
-- url     : https://prove2.me/theorems/cebdb924-8462-4658-b78a-5b6b0d447b9b
-- title:
--   WA diag p4: small Def_D preamble + sourceCertificate type
-- statement:
--   Diagnostic target (private): the `sourceCertificate_result8_3` type with a minimal preamble that imports only `Definitions.Def_Kyprianou_Ch08_StageCFoundation_D`, paired with the exact solution that WA'd on `open_result8_3`, to test whether the 88821-byte preamble is necessary for the failure.
-- source:
--   internal diagnostic

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false

theorem waDiag.p4 : Kyprianou.Ch08.StageB.sourceCertificate_result8_3 := by sorry
