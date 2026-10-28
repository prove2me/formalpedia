-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_card_eq_three_n_sub_six
-- name    : WilliamsonShmoys.exists_planar_supergraph_card_eq_three_n_sub_six
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:35:00.364377+00:00
-- url     : https://prove2.me/theorems/34ab6217-99ed-4ad8-851a-598b74fb942c
-- title:
--   Planar graphs admit a triangulated supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_card_eq_three_n_sub_six
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
