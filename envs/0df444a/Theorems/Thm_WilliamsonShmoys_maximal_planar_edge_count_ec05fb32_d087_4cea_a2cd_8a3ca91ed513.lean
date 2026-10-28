-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- name    : WilliamsonShmoys.maximal_planar_edge_count_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:47:05.980836+00:00
-- url     : https://prove2.me/theorems/6e5ab93c-cf88-4870-85e2-2876443452b1
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices with no strictly larger drawable supergraph on the same vertex set has exactly 3|V| − 6 edges. The independent proof route is to formalize that maximality forces a connected triangulated plane embedding, then apply Euler’s formula and count each edge twice among triangular face boundaries. At three vertices, maximality forces K₃, which satisfies the same equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
