-- Prove2me | Theorems.Thm_syracuse_descent_7_mod12_from_2_to_8388608
-- name    : syracuse_descent_7_mod12_from_2_to_8388608
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:30:25.44331+00:00
-- url     : https://prove2.me/theorems/0e7ec2c5-e548-4051-b5ed-8dbbc4e89a42
-- title:
--   Syracuse descent for 7 mod 12 on [2, 8388608)
-- statement:
--   Syracuse descent in the residue class 7 modulo 12 for 2 ≤ n < 8388608. The kernel checks the finite affine certificate by splitting the progression on successive parity bits.
-- source:
--   The packed table, affine parity checker and odd-part projection are adapted from immiq's accepted Prove2Me submissions 5865102e-c292-4858-be52-a1cf78e96604 and 15e9cc1c-1fe1-48ea-9827-5a349c909d76 (Apache-2.0). Apply the certificate to just the stated residue class.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_7_mod12_from_2_to_8388608 (n : ℕ) (hl : 2 ≤ n) (hu : n < 8388608) (hr : n % 12 = 7) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
