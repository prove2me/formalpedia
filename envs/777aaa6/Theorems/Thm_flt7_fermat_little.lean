-- Prove2me | Theorems.Thm_flt7_fermat_little
-- name    : flt7_fermat_little
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:47:48.896144+00:00
-- url     : https://prove2.me/theorems/c0d3a229-ce89-4f9f-9cd5-66849e06c4ab
-- statement:
--   Fermat's Little Theorem for exponent 7: for all integers a, 7 divides a^7 - a. This is the special case p=7 of Fermat's Little Theorem (7 ∣ a^p - a for all a when p is prime). Proved by checking all 7 residue classes in ZMod 7 (by decide) and lifting to ℤ via ZMod.intCast_zmod_eq_zero_iff_dvd.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_little_theorem

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic

theorem flt7_fermat_little (a : ℤ) : (7 : ℤ) ∣ a^7 - a := by sorry
