-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:38.063563+00:00
-- url     : https://prove2.me/theorems/da86700a-52f0-47aa-a632-36580bc91863
-- title:
--   Add one drawable edge below the planar bound
-- statement:
--   If a drawable finite simple graph on at least three vertices has fewer than 3|V|−6 edges, one more edge can be added while preserving a drawing on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  sorry
