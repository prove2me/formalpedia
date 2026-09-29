-- Prove2me | Theorems.Thm_bp_flt_for_p_ge_5
-- name    : bp_flt_for_p_ge_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-20T01:04:08.813431+00:00
-- url     : https://prove2.me/theorems/62770684-f4bd-47c4-b175-5523e34f12ac
-- statement:
--   **Fermat's Last Theorem for prime exponents $p \geq 5$.** No positive naturals $a, b, c$ satisfy $a^p + b^p = c^p$ when $p$ is a prime $\geq 5$. Combined with Euler's proof for $p = 3$ and Fermat's for $n = 4$ (both already in Mathlib), this implies the full FLT — see [blueprint](https://imperialcollegelondon.github.io/FLT/blueprint.pdf) §2.3, `FermatLastTheorem.of_p_ge_5`.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Prime.Basic

theorem bp_flt_for_p_ge_5 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by sorry
