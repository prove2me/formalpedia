-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:14:10.842317+00:00
-- url     : https://prove2.me/theorems/78197bac-b1f6-4329-9e25-4553750a4c60
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable graph on at least three finite ordered vertices has exactly three times its vertex count minus six edges. This supplies the numerical conclusion after the first child supplies a maximal extension. The new proof route is to show maximality forces every face in a connected planar embedding to be triangular, apply Euler’s formula and the face-degree sum, and handle disconnectedness and the three-vertex case explicitly. At the boundary of three vertices, maximality gives the triangle and the equality reads 3 + 6 = 9. The supplied arc predicate and cited textbook source were inspected only at the statement/description level; formalizing the face and Euler reasoning for this model remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
