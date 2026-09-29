-- Prove2me | solution 1 for lean_workbook_plus_9468
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:42:42.575162+00:00
-- url     : https://prove2.me/submissions/b3ce7398-47c4-44b0-a4ec-45e0ea2a2a10

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : 6 ^ 2016 ≡ 1 [ZMOD 43] := by
  have h : (6 : ℤ)^3 ≡ 1 [ZMOD 43] := by norm_num [Int.ModEq]
  simpa only [← pow_mul,one_pow] using h.pow 672
