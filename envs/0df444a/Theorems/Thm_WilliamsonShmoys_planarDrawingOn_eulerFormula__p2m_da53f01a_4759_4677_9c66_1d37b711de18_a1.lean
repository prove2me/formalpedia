-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerFormula__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
-- name    : WilliamsonShmoys.planarDrawingOn_eulerFormula__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:28.54412+00:00
-- url     : https://prove2.me/theorems/bd7293c6-e84f-4a76-8bde-2e7b0da2a7be
-- title:
--   Euler face count from a planar drawing
-- statement:
--   A crossing-free drawing of a finite connected graph gives a face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_eulerFormula__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2 := by
  sorry
