-- Prove2me | Theorems.Thm_ClassicalGaps_lapMatrix_eq_orientedIncMatrix_mul_transpose
-- name    : ClassicalGaps.lapMatrix_eq_orientedIncMatrix_mul_transpose
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T20:24:33.788838+00:00
-- url     : https://prove2.me/theorems/35b0a676-2262-4a8e-9b63-a24522382743
-- title:
--   Laplacian matrix factors as (oriented incidence matrix) times its transpose
-- statement:
--   For a finite simple graph $G$, the Laplacian matrix $L = D - A$ equals $B B^\top$, where $B$ is the oriented (signed) incidence matrix of $G$ obtained from an arbitrary vertex ordering. This is the standard algebraic bridge used in the proof of Kirchhoff's matrix-tree theorem: it lets a cofactor of $L$ be computed via the Cauchy-Binet formula applied to $B$. It is a child lemma of `ClassicalGaps.kirchhoff_matrix_tree`.
--
--   Formalization Note: fills the gap noted in Mathlib's `SimpleGraph.IncMatrix` TODO ('Define the graph Laplacian of a simple graph using the oriented incidence matrix from an arbitrary orientation'), using the newly published `Definitions.Def_ClassicalGaps_orientedIncMatrix`.

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix
open Classical Matrix

namespace ClassicalGaps

theorem lapMatrix_eq_orientedIncMatrix_mul_transpose {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.lapMatrix ℝ = orientedIncMatrix G * (orientedIncMatrix G)ᵀ := by sorry

end ClassicalGaps
