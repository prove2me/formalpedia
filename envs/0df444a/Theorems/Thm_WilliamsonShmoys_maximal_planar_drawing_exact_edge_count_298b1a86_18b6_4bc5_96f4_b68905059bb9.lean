-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:10:34.669868+00:00
-- url     : https://prove2.me/theorems/ae1e9695-fe66-4fae-a2a9-9434df71a322
-- title:
--   Edge count of a maximal drawn graph (job-specific declaration)
-- statement:
--   An inclusion-maximal drawn simple graph on at least three vertices has exactly 3|V|−6 edges. The proof must show that maximality forces a connected triangulation for this arc-drawing predicate, then derive the count from Euler’s formula and face-edge incidence counting. At three vertices, maximality forces all three possible edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_298b1a86_18b6_4bc5_96f4_b68905059bb9
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  sorry
