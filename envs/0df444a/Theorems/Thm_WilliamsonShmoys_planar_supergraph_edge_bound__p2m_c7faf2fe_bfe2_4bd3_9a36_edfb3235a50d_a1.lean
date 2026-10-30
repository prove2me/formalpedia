-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_c7faf2fe_bfe2_4bd3_9a36_edfb3235a50d_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound__p2m_c7faf2fe_bfe2_4bd3_9a36_edfb3235a50d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:03:43.206973+00:00
-- url     : https://prove2.me/theorems/a35190bf-fe1a-4d87-ab3a-82a6067f7e12
-- title:
--   Planar supergraph edge lower bound
-- statement:
--   Every drawable finite graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is at least 3|V|−6. This is the planar augmentation step: extend the drawing to a triangulated planar graph, then apply Euler’s formula and count edge-face incidences. The three-vertex boundary case gives the lower bound 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_bound__p2m_c7faf2fe_bfe2_4bd3_9a36_edfb3235a50d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ L : SimpleGraph V,
      LE.le K L ∧
      HasPlanarDrawingOn L ∧
      LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6) := by
  sorry
