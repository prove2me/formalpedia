-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_reachable_pair__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
-- name    : WilliamsonShmoys.planar_drawing_add_reachable_pair__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:56.512192+00:00
-- url     : https://prove2.me/theorems/01b2b8bc-0ae1-444c-bc1d-4b7d129cd719
-- title:
--   Add a drawable bridge between two components
-- statement:
--   Given a finite drawing and two vertices in different components, add edges to obtain a supergraph that still has a drawing and in which those vertices are connected by a path. A proof can find a face incident to two components and draw a simple joining arc inside that face; the central work is formalizing the face and arc construction while preserving all existing arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_reachable_pair__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) {a b : V}
    (hab : ¬ H.Reachable a b) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Reachable a b := by sorry
