-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_3649950b_31dd_4927_b1e8_a61f090b394f_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_3649950b_31dd_4927_b1e8_a61f090b394f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:11.644198+00:00
-- url     : https://prove2.me/theorems/98d2ce50-16ca-4db3-bebc-b1953e5d6a1b
-- title:
--   Triangulation completion with exact edge count
-- statement:
--   Every drawable simple graph on a fixed finite ordered vertex set of size at least three extends to a drawable graph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_3649950b_31dd_4927_b1e8_a61f090b394f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel U.Adj := Classical.decRel U.Adj
       U.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
