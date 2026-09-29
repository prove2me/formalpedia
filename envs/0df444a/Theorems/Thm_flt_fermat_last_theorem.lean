-- Prove2me | Theorems.Thm_flt_fermat_last_theorem
-- name    : flt.fermat_last_theorem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/df8d438b-9744-59a8-8ac0-819255e96ba6
-- title:
--   Fermat's Last Theorem
-- statement:
--   The theorem asserts: for every natural number $n$ with $3 \le n$, and for all natural numbers $a, b, c$ with $0 < a$, $0 < b$ and $0 < c$, one has $a^n + b^n \neq c^n$. Every quantity occurring is a natural number; the arithmetic is the arithmetic of $\mathbb{N}$, so the equation is the unsigned one and no rearrangement with signs is involved. The three positivity hypotheses are stated separately, one for each of $a$, $b$, $c$; they exclude exactly the degenerate identities $0^n + b^n = b^n$ and $a^n + 0^n = a^n$ (and, with $c = 0$, the impossible $a^n + b^n = 0$). The hypothesis $3 \le n$ restricts the exponent: nothing is claimed for $n \le 2$; indeed for $n = 1, 2$ the conclusion fails, since $1^1 + 1^1 = 2^1$ and $3^2 + 4^2 = 5^2$. The conclusion is a negation of an equality of natural numbers, quantified over all admissible $n, a, b, c$ simultaneously; it is the elementary, fully unfolded form of Fermat's assertion, using no project-specific notion and only Mathlib's natural numbers and their power operation.
--
--   This is Fermat's Last Theorem in its elementary spelling, the statement proved by Wiles, with Taylor–Wiles, completing the chain through Frey, Serre and Ribet. Mathlib's own formulation is the predicate `FermatLastTheorem`, namely $\forall n \ge 3$, $\forall a, b, c$ nonzero natural numbers, $a^n + b^n \neq c^n$; that version phrases the nondegeneracy as $a \neq 0$ rather than $0 < a$, and the two formulations are interderivable in one step each way. Being the top-level assertion, it is not used as an input anywhere else in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_fermat_last_theorem.lean

import Mathlib.NumberTheory.FLT.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem flt.fermat_last_theorem (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n := by sorry
