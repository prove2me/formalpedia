-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2_maximal_extension
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:23:44.857544+00:00
-- url     : https://prove2.me/theorems/fb23c773-4556-453b-808d-47a04bf70778
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable graph
-- statement:
--   Any graph with a drawing witness on a finite ordered vertex type can be extended to a drawable graph on the same type that is inclusion-maximal among drawable supergraphs. The at-least-three-vertices hypothesis is retained for the intended triangulation route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L ≤ M ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M := by sorry
