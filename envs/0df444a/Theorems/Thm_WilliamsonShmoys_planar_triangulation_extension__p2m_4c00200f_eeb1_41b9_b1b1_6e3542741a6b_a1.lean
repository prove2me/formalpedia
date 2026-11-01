-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_4c00200f_eeb1_41b9_b1b1_6e3542741a6b_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_4c00200f_eeb1_41b9_b1b1_6e3542741a6b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:17.360033+00:00
-- url     : https://prove2.me/theorems/a05c061d-946f-411a-b5cf-34f022290b66
-- title:
--   Triangulated extension of a finite planar graph
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable simple supergraph on the same vertices with exactly three times the number of vertices minus six edges. The extension is constructed by triangulating the faces of a planar embedding and counting with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_4c00200f_eeb1_41b9_b1b1_6e3542741a6b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
