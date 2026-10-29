-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_disconnected__p2m_9bb32eb0_a144_4276_9cbf_a7f4026975ff_a2
-- name    : WilliamsonShmoys.planar_drawing_add_edge_for_disconnected__p2m_9bb32eb0_a144_4276_9cbf_a7f4026975ff_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:56:45.70266+00:00
-- url     : https://prove2.me/theorems/ef70fa5c-2eee-4385-baf2-d66abdb9f5c8
-- title:
--   Extend a disconnected planar drawing by an edge
-- statement:
--   If a finite graph on an ordered vertex type has a crossing-free plane drawing and is disconnected, then its drawing can be extended by adding an edge between components, producing a drawable graph that strictly contains the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_for_disconnected__p2m_9bb32eb0_a144_4276_9cbf_a7f4026975ff_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hP : HasPlanarDrawingOn P) (hDisconnected : ¬ P.Connected) : ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ ¬ Q ≤ P := by sorry
