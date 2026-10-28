-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_euler_equations
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_for_euler_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:36:14.671564+00:00
-- url     : https://prove2.me/theorems/16de6deb-de5f-4a25-8b3a-216fac552bd1
-- title:
--   Edge count of a maximal drawable graph for Euler counting
-- statement:
--   A maximal drawable simple graph on at least three vertices has 3|V| − 6 edges, expressed without subtraction as |E| + 6 = 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_for_euler_equations {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → L = M) (hCard : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
