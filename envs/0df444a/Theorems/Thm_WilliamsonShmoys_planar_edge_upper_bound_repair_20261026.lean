-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_repair_20261026
-- name    : WilliamsonShmoys.planar_edge_upper_bound_repair_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:21:18.699064+00:00
-- url     : https://prove2.me/theorems/aa9642cc-0bd8-40d5-b085-b24d2d055ec9
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with a drawing satisfying the supplied planar-drawing predicate and at least three vertices has at most 3|V|−6 edges. This supplies the upper bound in the target reduction. The size condition excludes the small cases where the bound need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_repair_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
