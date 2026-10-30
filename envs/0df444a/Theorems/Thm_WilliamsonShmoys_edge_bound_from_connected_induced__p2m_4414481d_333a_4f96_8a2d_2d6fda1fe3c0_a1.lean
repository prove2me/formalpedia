-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_connected_induced__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- name    : WilliamsonShmoys.edge_bound_from_connected_induced__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:46:05.500813+00:00
-- url     : https://prove2.me/theorems/66ed8684-7720-4905-99a4-14d61ffeb91a
-- title:
--   Combine connected induced-subgraph edge bounds
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the planar edge bound, then the whole finite simple graph does too, provided the graph has at least three vertices. Decompose into connected components, apply the local bound to large components, and handle components of size one or two directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_from_connected_induced__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hLocal : ∀ (S : Finset V), 3 ≤ S.card → (L.induce (↑S : Set V)).Connected → (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
