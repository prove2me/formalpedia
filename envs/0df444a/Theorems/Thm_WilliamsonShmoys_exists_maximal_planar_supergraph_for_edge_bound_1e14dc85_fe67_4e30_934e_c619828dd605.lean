-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:32:57.485997+00:00
-- url     : https://prove2.me/theorems/9000a10c-1aae-4317-b33b-1b55efdd5640
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every finite simple graph with a crossing-free drawing has a supergraph on the same vertex set that is inclusion-maximal among planar supergraphs. No lower bound on the number of vertices is needed for this finite maximality step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDrawing : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  sorry
