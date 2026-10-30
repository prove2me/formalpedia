-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_below_maximal_edge_bound
-- name    : WilliamsonShmoys.planar_extension_below_maximal_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:01:40.305901+00:00
-- url     : https://prove2.me/theorems/4e088d96-7c6f-4116-8b4d-1c891bb669d2
-- title:
--   Augment drawable graphs below the maximal planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices with fewer than 3|V| − 6 edges has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_below_maximal_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hE : U.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V, U ≤ W ∧ ¬ W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn W := by sorry
