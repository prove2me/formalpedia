-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_repair2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_repair2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:48:19.808984+00:00
-- url     : https://prove2.me/theorems/8add77fe-1a60-4528-bb17-f2784979ad0d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V, N ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N)
    (hV : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
