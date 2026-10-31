-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_iterate_bridges__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1
-- name    : WilliamsonShmoys.planar_drawing_iterate_bridges__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:54.531633+00:00
-- url     : https://prove2.me/theorems/f804bd63-0b59-452f-96bc-32a2449523dd
-- title:
--   Iterate planar bridge extensions to connect the graph
-- statement:
--   If every disconnected drawn supergraph of H admits a drawn supergraph extension that connects some previously disconnected pair, then H has a connected drawn supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_iterate_bridges__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (bridgeStep : ∀ (G : SimpleGraph V), H ≤ G → HasPlanarDrawingOn G → ¬ G.Connected → ∃ G' : SimpleGraph V, G ≤ G' ∧ HasPlanarDrawingOn G' ∧ ∃ u v : V, ¬ G.Reachable u v ∧ G'.Reachable u v) : ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
