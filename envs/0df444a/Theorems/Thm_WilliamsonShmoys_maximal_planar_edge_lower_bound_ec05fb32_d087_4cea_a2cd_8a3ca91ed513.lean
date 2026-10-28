-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:51:59.439833+00:00
-- url     : https://prove2.me/theorems/903569c9-3a5d-434c-a683-62c101831e7e
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A maximal simple graph with a planar drawing on at least three vertices has at least 3|V| − 6 edges. The independent route is to show maximality forces a triangulated embedding, then use Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
