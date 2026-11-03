-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_extension__p2m_67af1d40_5710_49f6_8447_77c85edb00fd_a1
-- name    : WilliamsonShmoys.triangulation_extension__p2m_67af1d40_5710_49f6_8447_77c85edb00fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:12.065858+00:00
-- url     : https://prove2.me/theorems/5d7adedc-405a-4aa7-a840-9d1b809cbdd4
-- title:
--   Drawable graph extension with triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_extension__p2m_67af1d40_5710_49f6_8447_77c85edb00fd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        (letI : DecidableRel M.Adj := Classical.decRel M.Adj
         M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
