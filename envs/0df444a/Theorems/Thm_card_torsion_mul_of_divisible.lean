-- Prove2me | Theorems.Thm_card_torsion_mul_of_divisible
-- name    : card_torsion_mul_of_divisible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/3cbac521-f5ff-561e-9b10-6a7a188fd6b4
-- title:
--   Multiplicativity of torsion cardinalities in a divisible abelian group
-- statement:
--   Let $A$ be an additive commutative group which is divisible in the sense that for every natural number $m \neq 0$ and every $x \in A$ there exists $y \in A$ with $m \cdot y = x$. Let $a, b$ be natural numbers with $a \neq 0$, and suppose that the subtypes $\{x \in A : a \cdot x = 0\}$ and $\{x \in A : b \cdot x = 0\}$ are both finite. The conclusion is the conjunction of two assertions: first, that $\{x \in A : (ab) \cdot x = 0\}$ is finite, and second, that its cardinality (as computed by `Nat.card`) equals the product of the cardinalities of $\{x \in A : a \cdot x = 0\}$ and $\{x \in A : b \cdot x = 0\}$. Here the scalar actions are by natural numbers, and no coprimality of $a$ and $b$ is assumed; note that $b$ is allowed to be $0$, in which case the hypothesis that $\{x : b \cdot x = 0\} = A$ is finite forces $A$ to be finite.
--
--   This is the classical multiplicativity of torsion orders coming from the exact sequence $0 \to A[a] \to A[ab] \xrightarrow{a} A[b] \to 0$ available in a divisible abelian group. It is used in the treatment of torsion in degree-zero Picard groups of curves, feeding the bounds [`AlgebraicCurve.Pic0.finite_and_card_torsion_le_of_natCast_ne_zero`](thm.html#AlgebraicCurve.Pic0.finite_and_card_torsion_le_of_natCast_ne_zero) and [`AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero`](thm.html#AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_card_torsion_mul_of_divisible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Function

theorem card_torsion_mul_of_divisible
    {A : Type*} [AddCommGroup A]
    (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ x : A, ∃ y : A, m • y = x)
    (a b : ℕ) (ha : a ≠ 0)
    (hfa : Finite {x : A // a • x = 0}) (hfb : Finite {x : A // b • x = 0}) :
    Finite {x : A // (a * b) • x = 0} ∧
      Nat.card {x : A // (a * b) • x = 0} =
        Nat.card {x : A // a • x = 0} * Nat.card {x : A // b • x = 0} := by sorry
