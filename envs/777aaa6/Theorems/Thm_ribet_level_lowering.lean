-- Prove2me | Theorems.Thm_ribet_level_lowering
-- name    : ribet_level_lowering
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-11T08:33:47.26367+00:00
-- url     : https://prove2.me/theorems/45086644-c77e-44e1-bf5d-5c6654d226bb
-- statement:
--   **Ribet's level-lowering theorem (ε-conjecture).** Given a coprime FLT counterexample $(a,b,c,p)$ with $p \geq 5$ prime, the mod-$p$ Galois representation $\rho_{E,p}$ attached to the Frey curve $E$ is irreducible and arises from a weight-2, level-$N$ newform where $N \mid 2$. Since there are no such nonzero newforms (the space $S_2(\Gamma_0(2))$ is empty), this is a contradiction.
-- source:
--   https://doi.org/10.1007/BF01231195

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem ribet_level_lowering (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) : False := by sorry
