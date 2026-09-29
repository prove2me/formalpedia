-- Prove2me | Theorems.Thm_flt5_gcd_rs_coprime
-- name    : flt5_gcd_rs_coprime
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-14T17:05:06.219342+00:00
-- url     : https://prove2.me/theorems/0edd65dd-91f3-44ee-bda7-0ce5e5e90a0c

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

theorem flt5_gcd_rs_coprime (r s w v : ℤ) (hcop : Int.gcd w v = 1) (hr : w = r ^ 5) (hs : v = s ^ 5) : Int.gcd r s = 1 := by sorry
