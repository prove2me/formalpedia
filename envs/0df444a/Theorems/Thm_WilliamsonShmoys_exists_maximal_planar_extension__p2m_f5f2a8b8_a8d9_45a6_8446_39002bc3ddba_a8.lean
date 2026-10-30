-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:17:33.535984+00:00
-- url     : https://prove2.me/theorems/2f6c2ed6-31e4-43e8-979f-aaed8ee2826b
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that cannot be strictly extended while remaining drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      Set.Subset K.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V,
        Set.Subset H.edgeSet H'.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn H' →
        H'.edgeSet = H.edgeSet := by
  sorry
