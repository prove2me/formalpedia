-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_33fd9cf6_5dff_42ab_8e0f_e49b055267c2_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_33fd9cf6_5dff_42ab_8e0f_e49b055267c2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:40:28.004841+00:00
-- url     : https://prove2.me/theorems/cf58cc9e-f646-47fb-8fd2-36c30afa08a0
-- title:
--   Edge bound from planar triangulation extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set with at least three vertices has a drawable supergraph on that same vertex set with at least 3|V|−6 edges. The child isolates the augmentation and planar edge-count argument; the parent uses maximality to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_33fd9cf6_5dff_42ab_8e0f_e49b055267c2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel _;
       3 * Fintype.card V - 6 <= K.edgeFinset.card) := by sorry
