-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_exact_edge_count_completion
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_for_exact_edge_count_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:53:06.500991+00:00
-- url     : https://prove2.me/theorems/f61b373b-c663-4f0a-8b6b-65f4433b9ecc
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   A drawable graph on a finite vertex type has a drawable supergraph that is inclusion-maximal among drawable graphs on that vertex type. Finiteness ensures a maximal element exists in the set of drawable supergraphs containing N.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_for_exact_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
