-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph
-- name    : WilliamsonShmoys.planar_drawing_dense_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:38:43.20653+00:00
-- url     : https://prove2.me/theorems/e0a4f00d-5c7f-43c4-90b9-48180ebdf751
-- title:
--   Dense planar supergraph extension
-- statement:
--   Any graph on at least three vertices with the supplied planar drawing has a planar supergraph on the same vertex type with at least 3|V|−6 edges. Extend the finite graph to an inclusion-maximal planar supergraph while preserving the drawing; the standard planar augmentation and Euler argument gives the bound. The parent’s maximality hypothesis then forces this K to equal H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_dense_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
