-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
-- name    : WilliamsonShmoys.planar_drawing_on_maximal_extension__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:34.90992+00:00
-- url     : https://prove2.me/theorems/91e364bf-b9bd-4e87-9ab2-ce90ae6c4216
-- title:
--   Extend a planar drawing to an edge-maximal one
-- statement:
--   Any crossing-free drawing on a finite vertex set with at least three vertices extends, on the same vertex set, to an edge-maximal crossing-free drawing; the extension contains the original edges and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_maximal_extension__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V, N ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       N.edgeFinset.card ≤ M.edgeFinset.card) ∧
      ∀ M' : SimpleGraph V, HasPlanarDrawingOn M' → M ≤ M' → M' = M := by sorry
