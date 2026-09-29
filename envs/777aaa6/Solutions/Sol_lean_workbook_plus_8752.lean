-- Prove2me | solution 1 for lean_workbook_plus_8752
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:22.441708+00:00
-- url     : https://prove2.me/submissions/22c05a12-3342-44b7-9725-df634dcc0eff

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : 2 ^ 2000 ≡ 9 [MOD 13] := by
  have h : (2:ℕ)^12 ≡ 1 [MOD 13] := by norm_num [Nat.ModEq]
  have h1 : (2:ℕ)^1992 ≡ 1 [MOD 13] := by
    simpa only [←pow_mul,one_pow,show 12*166=1992 by decide] using h.pow 166
  have h2 : (2:ℕ)^8 ≡ 9 [MOD 13] := by norm_num [Nat.ModEq]
  simpa only [←pow_add,show 1992+8=2000 by decide,one_mul] using h1.mul h2
