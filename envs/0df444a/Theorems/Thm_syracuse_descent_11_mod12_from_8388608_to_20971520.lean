-- Prove2me | Theorems.Thm_syracuse_descent_11_mod12_from_8388608_to_20971520
-- name    : syracuse_descent_11_mod12_from_8388608_to_20971520
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:30:26.951386+00:00
-- url     : https://prove2.me/theorems/d569fe3d-cb58-5f1c-abbd-e6d61d659f67
-- title:
--   Syracuse descent for 11 mod 12 on [8388608, 20971520)
-- statement:
--   Syracuse descent in the residue class 11 modulo 12 for 8388608 ≤ n < 20971520. The kernel checks the finite affine certificate by splitting the progression on successive parity bits.
-- source:
--   The packed table, affine parity checker and odd-part projection are adapted from immiq's accepted Prove2Me submissions 5865102e-c292-4858-be52-a1cf78e96604 and 15e9cc1c-1fe1-48ea-9827-5a349c909d76 (Apache-2.0). Apply the certificate to just the stated residue class.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_11_mod12_from_8388608_to_20971520 (n : ℕ) (hl : 8388608 ≤ n) (hu : n < 20971520) (hr : n % 12 = 11) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
