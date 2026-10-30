-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_card_maximal_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_card_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:51:10.270703+00:00
-- url     : https://prove2.me/theorems/6a5dd28f-2326-433e-8b91-8d8c26373ca9
-- title:
--   A maximum-edge drawable graph has 3n−6 edges
-- statement:
--   If L has maximum edge count among drawable supergraphs of itself and has at least three vertices, then it has exactly 3|V|−6 edges. Maximum edge count gives inclusion-maximality; the remaining work is the planar triangulation and Euler-formula argument, including the disconnected case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_card_maximal_edge_count {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet.ncard ≤ L.edgeSet.ncard) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
