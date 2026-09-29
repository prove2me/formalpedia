-- Prove2me | Theorems.Thm_buchholz_double_factorial_constant_bound
-- name    : buchholz_double_factorial_constant_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T21:40:34.181372+00:00
-- url     : https://prove2.me/theorems/1b267629-05db-442a-b471-8ccdb18ec45a
-- statement:
--   Buchholz double-factorial optimal-constant bound (matrix Khintchine bridge (c)). For every integer $n \ge 1$, the pairing count $\binom{2n}{n}\!\cdot\! n!/2^n = (2n)!/(2^n n!) = (2n-1)!!$ satisfies $\left((2n)!/(2^n n!)\right)^{1/(2n)} \le \sqrt{2}\,\sqrt{2n}$. This is the source of the $\sqrt{q}$ factor in the noncommutative (matrix) Khintchine constant: with $q = 2n$, $((2n)!/(2^n n!))^{1/(2n)} \sim \sqrt{2n}$ is Buchholz's optimal constant $D_{2n}$. Proof: the elementary finite inequality $(2n-1)!! \le (2n)^n$, equivalently $(2n)! \le (2n)^n \cdot 2^n \cdot n!$ (by induction on $n$), then take $2n$-th roots: $((2n)!/(2^n n!))^{1/(2n)} \le ((2n)^n)^{1/(2n)} = \sqrt{2n} \le \sqrt{2}\,\sqrt{2n}$.
-- source:
--   Buchholz, Operator Khintchine inequality in non-commutative probability, Math. Ann. 319 (2001) 1-16, §2 (optimal constant D_{2n}=((2n)!/(2^n n!))^{1/2n}); CR2009 (arXiv:0805.4471) §6.1 Lemma 6.1.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

theorem buchholz_double_factorial_constant_bound
    (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)))
        ^ ((1 : ℝ) / (2 * n)) ≤ Real.sqrt 2 * Real.sqrt (2 * n) := by sorry
