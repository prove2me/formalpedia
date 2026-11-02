-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_from_bridge_step__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:41.46735+00:00
-- url     : https://prove2.me/theorems/fe1c41f8-8086-4f84-bd8f-45d16a4fd3f9
-- title:
--   Obtain a connected extension from bridge insertions
-- statement:
--   Reduce the bridge insertion step to the target by choosing a drawable supergraph containing G that is maximal under edge inclusion. If it is disconnected, the bridge-step hypothesis adds an edge between previously unreachable vertices, producing a strictly larger drawable supergraph and contradicting maximality. Finiteness of the simple graphs on V supplies the maximal graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2 {V : Type} [Fintype V] [LinearOrder V] (hStep : ∀ X : SimpleGraph V, ¬ X.Connected → HasPlanarDrawingOn X → ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧ ∃ u v : V, ¬ X.Reachable u v ∧ Y.Adj u v) (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hconn : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
