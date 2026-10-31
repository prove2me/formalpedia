-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count__p2m_8fdb4f78_7a22_4d46_bd0b_609fa5b74b25_a1
-- name    : WilliamsonShmoys.planar_augmentation_edge_count__p2m_8fdb4f78_7a22_4d46_bd0b_609fa5b74b25_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:28.113808+00:00
-- url     : https://prove2.me/theorems/04736d40-a8e2-4a01-9968-14670118dd12
-- title:
--   Planar augmentation to the maximal planar edge count
-- statement:
--   Every finite simple graph with the specified planar drawing and at least three vertices is contained in a planar supergraph on the same vertices whose edge count is exactly 3|V| − 6. This is the augmentation step: connect components and triangulate faces, then count edges using Euler’s formula and face-edge incidence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_edge_count__p2m_8fdb4f78_7a22_4d46_bd0b_609fa5b74b25_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
