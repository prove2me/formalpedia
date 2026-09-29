-- Prove2me | Theorems.Thm_flt_wiles
-- name    : flt_wiles
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-15T06:39:54.542099+00:00
-- url     : https://prove2.me/theorems/d2ed65b1-8a44-4c33-a61c-804d6d588b03
-- statement:
--   Fermat's Last Theorem for prime exponents p≥7, proved via the Wiles-Taylor modularity theorem (1995) combined with Ribet's level-lowering theorem (1990) and the Frey curve construction.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem flt_wiles (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by sorry
