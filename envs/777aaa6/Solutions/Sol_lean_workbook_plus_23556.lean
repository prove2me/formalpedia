-- Prove2me | solution 1 for lean_workbook_plus_23556
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:17.906348+00:00
-- url     : https://prove2.me/submissions/5bec89be-0cbf-425a-8516-39a68f8511bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ k : ℕ, 10 ^ (3 * k) ≡ 1 [ZMOD 111] := by
  intro k
  have h : (10 : ℤ)^3 ≡ 1 [ZMOD 111] := by norm_num [Int.ModEq]
  simpa only [← pow_mul,one_pow] using h.pow k
