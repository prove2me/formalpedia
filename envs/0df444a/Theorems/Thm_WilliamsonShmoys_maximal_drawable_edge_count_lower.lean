-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:05:28.697145+00:00
-- url     : https://prove2.me/theorems/a52f820a-fcde-4ee1-943b-4cd1dc9d670d
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
