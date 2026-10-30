-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_inclusion_maximal_to_triangular_map__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
-- name    : WilliamsonShmoys.planar_inclusion_maximal_to_triangular_map__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T11:22:26.186045+00:00
-- url     : https://prove2.me/theorems/2101673b-57bc-4880-b328-955a83448419
-- title:
--   An inclusion-maximal drawable graph has a finite triangular map
-- statement:
--   A drawable finite simple graph on at least three vertices that has no drawable proper supergraph on the same vertices admits a finite triangular map.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_inclusion_maximal_to_triangular_map__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊆ K.edgeSet → K.edgeSet = H.edgeSet) :
    ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap H (Fin m)) := by sorry
