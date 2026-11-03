-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_61dc9438_8340_4e4c_b1c7_250f3c9d3d5d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_61dc9438_8340_4e4c_b1c7_250f3c9d3d5d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:39:45.944065+00:00
-- url     : https://prove2.me/theorems/804de7f6-f862-47b4-add3-5edea203f43e
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among planar supergraphs on the same vertex set has exactly 3|V| - 6 edges. The child removes the planar topology and face-incidence argument from the parent; the parent only needs the supplied Euler equation and linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_61dc9438_8340_4e4c_b1c7_250f3c9d3d5d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
