-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_3cf9c867_dcef_4284_9c77_b8f72e798b36_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_3cf9c867_dcef_4284_9c77_b8f72e798b36_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:37.416037+00:00
-- url     : https://prove2.me/theorems/aaf33811-225e-424c-a7fa-7688f68b512b
-- title:
--   Planar triangulation completion on the same vertex set
-- statement:
--   Every finite planar graph on at least three vertices is contained, on the same vertex set, in a planar graph with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_3cf9c867_dcef_4284_9c77_b8f72e798b36_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
