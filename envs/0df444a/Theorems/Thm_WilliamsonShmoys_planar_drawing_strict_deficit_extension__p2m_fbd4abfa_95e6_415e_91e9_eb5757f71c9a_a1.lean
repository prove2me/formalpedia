-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_deficit_extension__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
-- name    : WilliamsonShmoys.planar_drawing_strict_deficit_extension__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:22.897389+00:00
-- url     : https://prove2.me/theorems/8099c0e3-4f95-4442-9548-845ddaba434e
-- title:
--   A strict planar edge deficit admits an edge extension
-- statement:
--   A connected finite planar graph on at least three vertices whose edge count is strictly below 3|V|−6 has a proper planar supergraph on the same vertex set. The proposed route uses Euler’s formula and face boundary walks to find a face admitting a noncrossing diagonal. The strict deficit and connectedness are essential to this extension step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_strict_deficit_extension__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hConn : ∀ u v, Relation.ReflTransGen K.Adj u v)
    (hV : 3 ≤ Fintype.card V)
    (hDeficit : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ HasPlanarDrawingOn L := by sorry
