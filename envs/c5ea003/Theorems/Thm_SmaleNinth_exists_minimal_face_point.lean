-- Prove2me | Theorems.Thm_SmaleNinth_exists_minimal_face_point
-- name    : SmaleNinth.exists_minimal_face_point
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-06T17:54:01.426172+00:00
-- url     : https://prove2.me/theorems/f4d9c2c8-2d5b-4e07-9cba-3425fa0ec8ce
-- title:
--   A nonempty polyhedron contains a point of a face cut out by its tight constraints
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, and let
--   $$P = \{x \in \mathbb{R}^n : Ax \ge b\}$$
--   be the associated polyhedron. If $P$ is nonempty, then there are a point $x \in P$ and a set $I \subseteq \{1,\dots,m\}$ of row indices such that
--
--   1. every constraint indexed by $I$ is **tight** at $x$, that is $A_i x = b_i$ for all $i \in I$; and
--   2. the affine subspace those tight constraints define is contained in the polyhedron: every $y \in \mathbb{R}^n$ with $A_i y = b_i$ for all $i \in I$ already satisfies $Ay \ge b$.
--
--   This is the standard description of a **minimal face** of a polyhedron (Korte--Vygen, Proposition 3.9): a nonempty face is minimal exactly when it is the solution set of a subsystem of the defining inequalities taken with equality. The point $x$ is any point of such a minimal face and $I$ is the set of constraints active on it. The statement is what converts a geometric question about $P$ into a question about a system of linear *equations*, which is the first half of the Cramer--Hadamard size bound: once $I$ is fixed, a small solution of $A_I y = b_I$ is automatically a small point of $P$.
--
--   Degenerate situations are allowed. If $P = \mathbb{R}^n$ the choice $I = \emptyset$ works, and the second clause is then the assertion that every point lies in $P$. No boundedness, full-dimensionality, or nondegeneracy hypothesis is imposed, and $I$ need not be a maximal or a linearly independent set of rows.
-- source:
--   B. Korte, J. Vygen, Combinatorial Optimization: Theory and Algorithms, 6th ed., Springer 2018, Proposition 3.9 (minimal faces of a polyhedron) and Section 4.1 (Size of Vertices and Faces); cf. A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 8.4.

import Definitions.Def_Polyhedron

open Matrix LinearOptimization

theorem SmaleNinth.exists_minimal_face_point {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty) :
    ∃ (x : Fin n → ℝ) (I : Finset (Fin m)),
      x ∈ polyhedron A b ∧
      (∀ i ∈ I, A.mulVec x i = b i) ∧
      (∀ y : Fin n → ℝ, (∀ i ∈ I, A.mulVec y i = b i) → y ∈ polyhedron A b) := by
  sorry
