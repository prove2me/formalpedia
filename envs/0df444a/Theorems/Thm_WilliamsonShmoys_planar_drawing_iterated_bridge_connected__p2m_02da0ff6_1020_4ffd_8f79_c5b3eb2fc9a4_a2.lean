-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_iterated_bridge_connected__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
-- name    : WilliamsonShmoys.planar_drawing_iterated_bridge_connected__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T11:58:03.804121+00:00
-- url     : https://prove2.me/theorems/0af80b1b-71aa-442b-8d74-8d2dede5e5be
-- title:
--   Assemble a connected drawable extension from bridge steps
-- statement:
--   If every drawable supergraph of a finite graph can be extended by a drawable step connecting any selected unreachable pair, then there is a connected drawable supergraph. Choose an edge-maximal drawable supergraph from the finite set of graphs on V; a disconnected maximal choice would admit a strict bridge extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_iterated_bridge_connected__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hStep : ∀ (K : SimpleGraph V), H ≤ K → HasPlanarDrawingOn K →
      ∀ (a b : V), ¬ K.Reachable a b →
        ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Reachable a b) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Connected := by sorry
