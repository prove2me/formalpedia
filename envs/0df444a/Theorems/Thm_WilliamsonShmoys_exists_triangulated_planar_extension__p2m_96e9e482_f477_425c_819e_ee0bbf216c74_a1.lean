-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension__p2m_96e9e482_f477_425c_819e_ee0bbf216c74_a1
-- name    : WilliamsonShmoys.exists_triangulated_planar_extension__p2m_96e9e482_f477_425c_819e_ee0bbf216c74_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:42.075533+00:00
-- url     : https://prove2.me/theorems/1345f058-46fd-4b3f-bd68-5a032464e223
-- title:
--   Triangulated extension of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_planar_extension__p2m_96e9e482_f477_425c_819e_ee0bbf216c74_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
