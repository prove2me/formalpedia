-- Prove2me | solution 1 for Mpfx.two_zpow_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:03.867535+00:00
-- url     : https://prove2.me/submissions/69e78317-cf55-4914-9308-46856d8495ee

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Theorems.Thm_Mpfx_two_zpow_split_toNat

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {K : Type*} [Field K] [CharZero K] (c : ℤ) {e k : ℤ} (h : k ≤ e) :
    (c : K) * (2 : K) ^ e = ((c * (2 : ℤ) ^ (e - k).toNat : ℤ) : K) * (2 : K) ^ k := by
  rw [two_zpow_split_toNat h]; push_cast; ring
end Mpfx
