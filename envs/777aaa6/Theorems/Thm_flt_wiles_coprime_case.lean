-- Prove2me | Theorems.Thm_flt_wiles_coprime_case
-- name    : flt_wiles_coprime_case
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-11T08:33:43.038186+00:00
-- url     : https://prove2.me/theorems/19372753-88c5-4105-abfb-dc66d8449434
-- statement:
--   **Wiles's theorem: FLT for coprime triples.** For pairwise coprime positive integers $a, b, c$ and prime $p \geq 5$, we have $a^p + b^p \neq c^p$. This is the heart of Wiles's 1995 proof: the Frey curve $y^2 = x(x-a^p)(x+b^p)$ is semistable (Frey–Ribet), hence modular (Wiles–Taylor), but Ribet's level-lowering yields a weight-2 newform of level 2 — which doesn't exist.
-- source:
--   https://doi.org/10.2307/2118559

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt_wiles_coprime_case (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) : a ^ p + b ^ p ≠ c ^ p := by sorry
