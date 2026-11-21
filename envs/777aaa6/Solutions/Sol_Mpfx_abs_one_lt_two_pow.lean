-- Prove2me | solution 1 for Mpfx.abs_one_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:16.680782+00:00
-- url     : https://prove2.me/submissions/c66d268d-55a3-4f16-a162-0a99b4487685

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {p : ℕ} (hp : 0 < p) : |(1 : ℤ)| < 2 ^ p := by
  have h2 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ p := pow_le_pow_right₀ (by norm_num) hp
  simp only [abs_one]
  omega
end Mpfx
