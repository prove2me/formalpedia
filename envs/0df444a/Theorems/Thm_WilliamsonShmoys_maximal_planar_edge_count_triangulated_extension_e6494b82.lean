-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulated_extension_e6494b82
-- name    : WilliamsonShmoys.maximal_planar_edge_count_triangulated_extension_e6494b82
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:26:52.502988+00:00
-- url     : https://prove2.me/theorems/c4011bda-e2a2-4391-a47d-b4ea4febecd9
-- title:
--   Triangulated extension for maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices extends, on the same vertex type, to a drawable graph with exactly 3|V|−6 edges. At three vertices the extension is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_triangulated_extension_e6494b82
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
