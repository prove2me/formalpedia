-- Prove2me | Theorems.Thm_SmaleNinth_integer_subsystem_solution_bound
-- name    : SmaleNinth.integer_subsystem_solution_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-06T17:54:00.624229+00:00
-- url     : https://prove2.me/theorems/f4c6c02f-42ec-4a10-bd98-aaa743b293ef
-- title:
--   Cramer--Hadamard bound for a consistent integer subsystem
-- statement:
--   Let $U \ge 1$ be an integer, let $A \in \mathbb{Z}^{m \times n}$ and $b \in \mathbb{Z}^m$ have all entries bounded by $U$ in absolute value, and let $I \subseteq \{1,\dots,m\}$ be any set of row indices. If the subsystem
--   $$A_i y = b_i \qquad (i \in I)$$
--   has a real solution $x$, then it has a real solution $y$ with
--   $$|y_j| \;\le\; n!\,U^{\,n} \qquad \text{for every } j = 0,\dots,n-1 .$$
--
--   In words: a *consistent* system of linear equations with integer data of size at most $U$ admits a solution whose entries are bounded by an explicit quantity depending only on the number $n$ of variables and on $U$ -- the number of equations does not appear. The classical proof selects a maximal linearly independent set of $r$ rows of $A_I$, which defines the same solution set, then a set of $r$ linearly independent columns; setting the remaining $n - r$ coordinates to zero leaves a square nonsingular integer system, and Cramer's rule expresses each coordinate as a quotient of two $r \times r$ integer determinants. The denominator is a nonzero integer, so at least $1$ in absolute value, while the permutation expansion bounds the numerator by $r!\,U^{\,r} \le n!\,U^{\,n}$.
--
--   The hypothesis is stated as the existence of the particular solution $x$, so the assertion is genuinely about consistency and not about solvability of an arbitrary system; no rationality or integrality of $y$ is claimed, and none holds in general.
-- source:
--   B. Korte, J. Vygen, Combinatorial Optimization: Theory and Algorithms, 6th ed., Springer 2018, Section 4.1 (Size of Vertices and Faces), Theorem 4.4; D. Bertsimas, J. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 8.4; cf. A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Chapter 10.

import Definitions.Def_Polyhedron

open Matrix LinearOptimization

theorem SmaleNinth.integer_subsystem_solution_bound {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (I : Finset (Fin m))
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (x : Fin n → ℝ)
    (hx : ∀ i ∈ I, (A.map (Int.cast : ℤ → ℝ)).mulVec x i = (b i : ℝ)) :
    ∃ y : Fin n → ℝ,
      (∀ i ∈ I, (A.map (Int.cast : ℤ → ℝ)).mulVec y i = (b i : ℝ)) ∧
      (∀ j, |y j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n) := by
  sorry
