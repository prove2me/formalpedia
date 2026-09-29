-- Prove2me | Theorems.Thm_flt_wiles_coprime
-- name    : flt_wiles_coprime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-15T06:42:19.758705+00:00
-- url     : https://prove2.me/theorems/7e2ef875-6327-4ef3-b373-34882126b192
-- statement:
--   FLT for prime exponents p≥7 in the coprime case. Given pairwise coprime positive integers a,b,c with a^p+b^p=c^p for prime p≥7, derive a contradiction via the Frey curve construction, Wiles-Taylor modularity theorem, and Ribet's level-lowering theorem.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt_wiles_coprime (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) : a ^ p + b ^ p ≠ c ^ p := by sorry
