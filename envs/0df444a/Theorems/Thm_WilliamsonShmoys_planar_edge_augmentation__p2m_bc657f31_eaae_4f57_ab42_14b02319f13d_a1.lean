-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:37:51.339643+00:00
-- url     : https://prove2.me/theorems/ed14ce5d-db85-45e0-baef-0034f9db9e54
-- title:
--   A drawable graph below the planar edge bound has a strict drawable extension
-- statement:
--   For any drawable graph on at least three vertices whose edge count is strictly below 3|V|−6, some strict drawable supergraph exists on the same vertex type. This includes sparse and disconnected graphs; at three vertices, every graph with fewer than three edges can be extended by adding a missing edge. A proof route is to connect components within faces and then add noncrossing diagonals until the drawing is triangulated; Euler counting shows that a graph already at the bound cannot require such an addition. This isolates the topological augmentation argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hlt : U.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W ∧ U < W := by sorry
