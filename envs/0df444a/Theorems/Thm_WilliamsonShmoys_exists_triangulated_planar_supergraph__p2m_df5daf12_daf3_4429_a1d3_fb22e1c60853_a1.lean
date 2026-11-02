-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:23.649608+00:00
-- url     : https://prove2.me/theorems/1b95303a-4f95-40e4-980b-ac53e8480e68
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Any graph with the given planar drawing and at least three vertices has a planar supergraph on the same vertices whose edge count is exactly 3|V|−6. This removes the geometric extension, triangulation, and Euler-formula work from the parent. A proof route is finite edge augmentation preserving the drawing, followed by the fact that a maximal planar drawing with at least three vertices has triangular faces and Euler’s formula. At |V|=3 the claimed count is 3, as expected. The continuous-arc drawing predicate makes the augmentation and face arguments the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeFinset.card + 6 := by sorry
