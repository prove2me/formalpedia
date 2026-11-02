-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:03:22.187893+00:00
-- url     : https://prove2.me/theorems/c1b4f689-ce4a-40bb-ab72-071998d2bd64
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   If a graph on at least three vertices has a crossing-free drawing and no strictly larger planar supergraph on the same vertices, its edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hcard : 3 ≤ Fintype.card V) :
    ∀ [DecidableRel P.Adj], P.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
