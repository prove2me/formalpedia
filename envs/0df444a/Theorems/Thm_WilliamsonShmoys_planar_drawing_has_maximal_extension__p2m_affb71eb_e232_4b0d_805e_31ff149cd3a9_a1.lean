-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:07.015679+00:00
-- url     : https://prove2.me/theorems/d8eb9faa-7b6a-47f8-9dee-d4b2e8065d3d
-- title:
--   Every finite drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is edge-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_affb71eb_e232_4b0d_805e_31ff149cd3a9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by sorry
