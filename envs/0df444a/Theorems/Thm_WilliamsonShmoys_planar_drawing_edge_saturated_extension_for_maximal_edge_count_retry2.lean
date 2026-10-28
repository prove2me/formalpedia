-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2
-- name    : WilliamsonShmoys.planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:02:19.509906+00:00
-- url     : https://prove2.me/theorems/a49f77ed-d0fb-4f5d-bb7d-c9f1ed8652e4
-- title:
--   Finite saturated planar extension
-- statement:
--   Every planar drawing on a finite vertex type has a planar supergraph that is maximal among planar graphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L <= M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M <= L := by sorry
