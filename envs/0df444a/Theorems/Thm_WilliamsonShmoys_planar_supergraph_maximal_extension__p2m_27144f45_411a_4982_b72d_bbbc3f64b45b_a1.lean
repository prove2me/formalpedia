-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:35.095478+00:00
-- url     : https://prove2.me/theorems/870bfd2f-4ca1-482a-946e-00772601b2f5
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by
  sorry
