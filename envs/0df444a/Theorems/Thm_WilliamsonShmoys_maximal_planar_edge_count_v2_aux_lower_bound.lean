-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2_aux_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_v2_aux_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:42:38.330873+00:00
-- url     : https://prove2.me/theorems/ddd65173-dd4a-4511-85fe-9ab94bafb4b9
-- title:
--   Maximal drawable graphs attain the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable graphs on the same vertex type has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_v2_aux_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ (X : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn X →
      (∀ {u v}, W.Adj u v → X.Adj u v) → X = W) :
    3 * Fintype.card V - 6 <= W.edgeSet.ncard := by sorry
