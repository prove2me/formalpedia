-- Prove2me | Theorems.Thm_HefferonLinAlg_row_equivalent_iff_same_row_space
-- name    : HefferonLinAlg.row_equivalent_iff_same_row_space
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:10:35.232289+00:00
-- url     : https://prove2.me/theorems/df32d03e-781a-4af9-a1ca-8e968e8a2cba
-- title:
--   Row equivalence is sameness of row space
-- statement:
--   Two $m \times n$ matrices $A$ and $B$ over a field $K$ are row equivalent — that is, $B = MA$ for some invertible $M$ — if and only if the span of the rows of $A$ equals the span of the rows of $B$. This is where Chapter One's Linear Combination Lemma arrives: row reduction changes the rows but never the subspace they span, and that invariant is complete, which is what makes reduced echelon form a genuine canonical form for row equivalence.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter One, Section III.2 and Chapter Two, Section III.3, Lemma 3.5 / Theorem 3.7, pp. 66-74, 146-153

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem row_equivalent_iff_same_row_space
    {K : Type*} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K) :
    (∃ M : Matrix (Fin m) (Fin m) K, IsUnit M.det ∧ B = M * A) ↔
      Submodule.span K (Set.range A) = Submodule.span K (Set.range B) := by
  sorry

end HefferonLinAlg
