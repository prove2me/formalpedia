-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_exists__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:12:54.879893+00:00
-- url     : https://prove2.me/theorems/4b4b9056-f4d7-45ac-af92-ced005ac2376
-- title:
--   Existence of a maximal planar supergraph on the same vertices
-- statement:
--   Every drawable finite graph on the given vertex type is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_exists__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V,
        Set.Subset M.edgeSet N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        Set.Subset N.edgeSet M.edgeSet) := by sorry
