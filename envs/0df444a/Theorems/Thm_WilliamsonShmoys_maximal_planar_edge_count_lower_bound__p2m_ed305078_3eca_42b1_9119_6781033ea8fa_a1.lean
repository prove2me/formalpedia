-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:50.064235+00:00
-- url     : https://prove2.me/theorems/870fe399-b049-44c0-b9a7-7936a0914e85
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J)
    (dJ : DecidableRel J.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel J.Adj := dJ;
      3 * Fintype.card V - 6 ≤ J.edgeFinset.card) := by sorry
