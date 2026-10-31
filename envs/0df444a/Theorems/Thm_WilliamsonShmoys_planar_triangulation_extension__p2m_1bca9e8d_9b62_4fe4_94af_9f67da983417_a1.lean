-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_1bca9e8d_9b62_4fe4_94af_9f67da983417_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_1bca9e8d_9b62_4fe4_94af_9f67da983417_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:16:28.615107+00:00
-- url     : https://prove2.me/theorems/6f52b5a3-b090-4468-aa84-13620a15b574
-- title:
--   Extend a finite drawable graph to a triangulation with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_1bca9e8d_9b62_4fe4_94af_9f67da983417_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
