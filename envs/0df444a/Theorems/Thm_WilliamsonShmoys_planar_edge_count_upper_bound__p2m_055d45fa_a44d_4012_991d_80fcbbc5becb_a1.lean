-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:15.053586+00:00
-- url     : https://prove2.me/theorems/2c123b8f-1995-4892-9bf1-663a03a79ac0
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V| − 6 edges. This isolates the Euler-formula upper bound from the maximality argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
