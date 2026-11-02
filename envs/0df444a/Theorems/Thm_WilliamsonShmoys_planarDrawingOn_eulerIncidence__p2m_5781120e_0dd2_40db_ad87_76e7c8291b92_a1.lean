-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerIncidence__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
-- name    : WilliamsonShmoys.planarDrawingOn_eulerIncidence__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:07:42.056175+00:00
-- url     : https://prove2.me/theorems/da53f01a-4759-4677-9c66-1d37b711de18
-- title:
--   A planar drawing yields Euler and face-incidence counts
-- statement:
--   A crossing-free drawing of a finite connected simple graph with at least three vertices yields a number of faces and total face-boundary incidences satisfying Euler’s equation, two incidences per edge, and at least three incidences per face. A proof route derives a rotation system and its face walks from the drawing, applies Euler’s formula, and handles bridges by counting both sides. This removes the topological step from the parent; constructing and verifying those data is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_eulerIncidence__p2m_5781120e_0dd2_40db_ad87_76e7c8291b92_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ f i : ℕ,
      Fintype.card V + f = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2 ∧
      2 * (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ≤ i ∧
      3 * f ≤ i := by sorry
