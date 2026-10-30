-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_with_euler_edge_count_a4f892c9_f19c_464f_8d5c_153cf02f5773
-- name    : WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count_a4f892c9_f19c_464f_8d5c_153cf02f5773
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:02:14.503144+00:00
-- url     : https://prove2.me/theorems/d0c7f10e-35cd-48c0-b98e-d612581c45c6
-- title:
--   Drawable supergraph with Euler edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count_a4f892c9_f19c_464f_8d5c_153cf02f5773 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
