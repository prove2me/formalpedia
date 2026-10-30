-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_join_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1
-- name    : WilliamsonShmoys.planar_join_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:15.88073+00:00
-- url     : https://prove2.me/theorems/3aa5230c-4315-4ebe-89c1-e40f6294d530
-- title:
--   Join two components of a planar drawing by one edge
-- statement:
--   Given a planar drawing and two distinct vertices in different connected components, there is a planar drawing of a graph on the same vertices that retains every old edge and adds exactly the edge between those vertices. The endpoints are unrestricted within their components: the geometric proof must re-embed each component so the selected vertex can be reached from the exterior.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_join_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (u v : V) (huv : u ≠ v) (hsep : ¬ H.Reachable u v) : ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v ∧ ¬ H.Adj u v ∧ ∀ {x y : V}, G.Adj x y → H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
