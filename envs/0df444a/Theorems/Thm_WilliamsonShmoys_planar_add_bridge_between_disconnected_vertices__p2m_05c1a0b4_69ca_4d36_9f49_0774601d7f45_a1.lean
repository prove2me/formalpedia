-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_bridge_between_disconnected_vertices__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a1
-- name    : WilliamsonShmoys.planar_add_bridge_between_disconnected_vertices__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:36.016649+00:00
-- url     : https://prove2.me/theorems/3dd48983-b264-4c3c-82a7-94630b56a533
-- title:
--   Add a planar bridge between disconnected vertices
-- statement:
--   If two vertices of a finite planar graph are in different connected components, there is a planar supergraph on the same vertices containing the edge between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_bridge_between_disconnected_vertices__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hnot : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
