-- Prove2me | Theorems.Thm_HefferonLinAlg_row_rank_eq_column_rank
-- name    : HefferonLinAlg.row_rank_eq_column_rank
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:20:31.416918+00:00
-- url     : https://prove2.me/theorems/fd79887d-f5d3-4bba-9c3d-6197404acabe
-- title:
--   Row rank equals column rank
-- statement:
--   For any $m \times n$ matrix $A$ over a field $K$, the dimension of the span of the rows of $A$ equals the dimension of the span of the rows of its transpose — that is, of the columns of $A$. Row rank equals column rank. This is the bridge Hefferon builds between the matrix-of-numbers view of Chapter One and the vector-space view of Chapter Two, and it is what lets one speak of *the* rank of a matrix.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Two, Section III.3, Theorem 3.11, p. 150

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem row_rank_eq_column_rank
    {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    Module.finrank K (Submodule.span K (Set.range A)) =
      Module.finrank K (Submodule.span K (Set.range Aᵀ)) := by
  sorry

end HefferonLinAlg
