-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:44.16402+00:00
-- url     : https://prove2.me/theorems/1341e650-028f-415c-aaf6-59348f49d6ab
-- title:
--   Planar triangulation extension
-- statement:
--   Any finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
