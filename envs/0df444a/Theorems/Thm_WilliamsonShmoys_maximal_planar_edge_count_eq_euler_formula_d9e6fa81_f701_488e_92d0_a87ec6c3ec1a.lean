-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler_formula_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq_euler_formula_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:38:25.695197+00:00
-- url     : https://prove2.me/theorems/a4f892c9-f19c-464f-8d5c-153cf02f5773
-- title:
--   Euler edge count for a maximal drawable graph
-- statement:
--   A graph maximal among graphs with the specified planar drawing has exactly 3|V| − 6 edges when its finite vertex type has at least three elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq_euler_formula_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
