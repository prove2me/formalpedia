-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_accounting_implies_edge_bound
-- name    : WilliamsonShmoys.face_accounting_implies_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:08:26.396269+00:00
-- url     : https://prove2.me/theorems/12087d91-3069-4249-a63a-ff1ac9d3aee5
-- title:
--   Face accounting implies the planar edge bound
-- statement:
--   For a finite graph, Euler’s equation together with two boundary incidences per edge and at least three incidences per face implies the 3V−6 edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.face_accounting_implies_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hData : ∃ (f b : Nat),
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      2 * G.edgeSet.ncard = b ∧
      3 * f ≤ b) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
