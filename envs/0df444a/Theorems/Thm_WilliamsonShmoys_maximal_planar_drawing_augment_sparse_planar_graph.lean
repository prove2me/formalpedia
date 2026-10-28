-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_augment_sparse_planar_graph
-- name    : WilliamsonShmoys.maximal_planar_drawing_augment_sparse_planar_graph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:58:36.930105+00:00
-- url     : https://prove2.me/theorems/e5a48da6-dba2-48dc-ace6-fcdd81cb72e6
-- title:
--   Sparse planar drawings admit an addable edge
-- statement:
--   For a finite ordered vertex type with at least three vertices, a graph drawn without crossings and with fewer than 3|V|−6 edges has a drawable proper supergraph on the same vertex type. The conclusion explicitly witnesses a missing edge that can be added while retaining a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_augment_sparse_planar_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : T.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ U : SimpleGraph V, HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      ∃ u v, ¬ T.Adj u v ∧ U.Adj u v := by sorry
