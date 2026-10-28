-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:28:28.702494+00:00
-- url     : https://prove2.me/theorems/65502eb0-83ea-446d-8cd2-6e7ab9e51cd1
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most `3|V| − 6` edges, expressed without truncated subtraction as `edgeCount + 6 ≤ 3|V|`. The boundary `|V| = 3` is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
