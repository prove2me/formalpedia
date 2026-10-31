-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b4d3c156_327f_4a72_8089_248d3313a19e_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_b4d3c156_327f_4a72_8089_248d3313a19e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:12.445998+00:00
-- url     : https://prove2.me/theorems/62016e60-61d6-45b8-a392-007d59f3ecc6
-- title:
--   Every planar graph extends to a triangulation
-- statement:
--   Any drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This is the standard triangulation-extension result: repeatedly add an edge within a face when that face is not triangular, then use Euler’s formula. It removes the topological augmentation and edge-counting work from the parent; its proof still requires formalizing those arguments for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_b4d3c156_327f_4a72_8089_248d3313a19e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
