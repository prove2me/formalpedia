-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:56.774876+00:00
-- url     : https://prove2.me/theorems/9df70f0c-e392-4539-bc07-082cd2cf5417
-- title:
--   Edge-maximal planar supergraph extension
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a planar supergraph on the same vertices that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L.edgeSet ⊆ T.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V,
        T.edgeSet ⊆ U.edgeSet →
        (∃ e, e ∈ U.edgeSet ∧ e ∉ T.edgeSet) →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn U := by
  sorry
