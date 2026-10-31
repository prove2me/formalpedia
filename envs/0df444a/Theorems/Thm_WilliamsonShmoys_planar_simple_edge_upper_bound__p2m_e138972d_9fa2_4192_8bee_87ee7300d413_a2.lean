-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
-- name    : WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:40:54.048655+00:00
-- url     : https://prove2.me/theorems/e9f48628-0158-4b2d-9356-176e809609d8
-- title:
--   Drawable simple graphs have at most 3n − 6 edges
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3n − 6 edges. A proof route is Euler counting together with the fact that face boundary incidence is at least three after accounting for bridges and disconnected components, or by reducing to connected plane graphs while preserving the bound. The n ≥ 3 hypothesis is needed for this natural-number form.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
