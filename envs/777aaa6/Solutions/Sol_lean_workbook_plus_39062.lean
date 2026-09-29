-- Prove2me | solution 1 for lean_workbook_plus_39062
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:01.307239+00:00
-- url     : https://prove2.me/submissions/f382f6d0-90b5-43fa-b804-87d45ec03388

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : 7 ^ 2003 ≡ 3 [MOD 10] := by
  have h4 : (7 : ℕ)^4 ≡ 1 [MOD 10] := by norm_num [Nat.ModEq]
  have h2000 : (7 : ℕ)^2000 ≡ 1 [MOD 10] := by
    simpa only [← pow_mul,one_pow,show 4*500=2000 by decide] using h4.pow 500
  have h3 : (7 : ℕ)^3 ≡ 3 [MOD 10] := by norm_num [Nat.ModEq]
  simpa only [← pow_add,one_mul,show 2000+3=2003 by decide] using h2000.mul h3
