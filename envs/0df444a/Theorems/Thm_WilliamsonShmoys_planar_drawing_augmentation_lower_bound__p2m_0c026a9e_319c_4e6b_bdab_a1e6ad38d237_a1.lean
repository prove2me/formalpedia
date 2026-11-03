-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_lower_bound__p2m_0c026a9e_319c_4e6b_bdab_a1e6ad38d237_a1
-- name    : WilliamsonShmoys.planar_drawing_augmentation_lower_bound__p2m_0c026a9e_319c_4e6b_bdab_a1e6ad38d237_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:28.129335+00:00
-- url     : https://prove2.me/theorems/0835c3dc-b66c-4223-9284-2bc5bd7f2cf4
-- title:
--   Edge lower bound from planar drawing augmentation
-- statement:
--   Any graph with a drawing satisfying the target’s exact planar-drawing predicate, on at least three vertices, is a subgraph of a drawable graph on the same vertices with at least 3|V|−6 edges. The standard independent route is to augment the embedded graph to a triangulation and count edges by Euler’s formula; this child contains the remaining topological work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_augmentation_lower_bound__p2m_0c026a9e_319c_4e6b_bdab_a1e6ad38d237_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
       3 * Fintype.card V - 6 <= L.edgeFinset.card) := by sorry
