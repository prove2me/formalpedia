-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f78503a9_5416_4ae7_a29c_25625a9bc1b3_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_f78503a9_5416_4ae7_a29c_25625a9bc1b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:38:19.863991+00:00
-- url     : https://prove2.me/theorems/77670b4a-3d82-4709-99a1-b7afb10e3984
-- title:
--   Triangulation completion for a drawable graph
-- statement:
--   Any crossing-free drawing of a finite simple graph on at least three vertices can be extended, on the same vertex set, to a crossing-free drawing whose graph has exactly 3|V|−6 edges. This is the standard triangulation-completion result: add drawable edges until every face is triangular, then count edges using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_f78503a9_5416_4ae7_a29c_25625a9bc1b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
