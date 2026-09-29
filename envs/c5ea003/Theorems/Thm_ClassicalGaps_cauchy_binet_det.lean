-- Prove2me | Theorems.Thm_ClassicalGaps_cauchy_binet_det
-- name    : ClassicalGaps.cauchy_binet_det
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T20:28:19.624997+00:00
-- url     : https://prove2.me/theorems/ad9e84b1-2171-4dad-bee5-774e7caccf7d
-- title:
--   The Cauchy-Binet formula
-- statement:
--   For an $m \times n$ real matrix $A$ and $n \times m$ real matrix $B$ with $m \le n$, the Cauchy-Binet formula expresses $\det(AB)$ as $\sum_{S} \det(A_S)\det(B_S)$, summed over all $m$-element subsets $S$ of $\{1,\dots,n\}$, where $A_S$ (resp. $B_S$) is the $m\times m$ submatrix of $A$ (resp. $B$) keeping only the columns (resp. rows) indexed by $S$, reindexed to $\mathrm{Fin}\,m$ via the order isomorphism `Finset.orderIsoOfFin`.
--
--   This is a foundational, widely reusable linear-algebra identity (special cases include $\det(AB)=\det A\det B$ when $m=n$, and the Gram determinant expansion). It is not yet in Mathlib. It is a child lemma of `ClassicalGaps.kirchhoff_matrix_tree`, where it is applied to the oriented incidence matrix to reduce a cofactor of the graph Laplacian to a sum of squared minors indexed by edge subsets.

import Mathlib
open Classical Matrix Finset

theorem ClassicalGaps.cauchy_binet_det {m n : ℕ} (hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if hS : S.card = m then
        (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
        (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
      else 0 := by sorry
