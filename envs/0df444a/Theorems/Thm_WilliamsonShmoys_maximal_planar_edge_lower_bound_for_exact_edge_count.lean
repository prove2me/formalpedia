-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_for_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:22:22.993537+00:00
-- url     : https://prove2.me/theorems/b875804a-d0ae-4f73-9a83-bae2ae328f49
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   A graph with a crossing-free drawing that has no drawable supergraph on the same vertices has at least 3|V|−6 edges. For three vertices, maximality forces the triangle. In larger cases, the intended proof establishes connectedness and 2-connectedness, uses maximality to show every face is triangular, and combines the face-edge incidence count with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_for_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
