-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_edge_count__p2m_adaa59b8_bbaf_4393_8e55_4a0450b92ec8_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count__p2m_adaa59b8_bbaf_4393_8e55_4a0450b92ec8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:58.795108+00:00
-- url     : https://prove2.me/theorems/b6eb2a76-7845-4b9d-82ab-24d9043bea47
-- title:
--   Maximal planar extension of a finite drawing
-- statement:
--   Any drawn simple graph on at least three vertices has a drawn supergraph on the same vertices whose edge count is exactly 3n−6, and the original edge count does not exceed the extension's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count__p2m_adaa59b8_bbaf_4393_8e55_4a0450b92ec8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
