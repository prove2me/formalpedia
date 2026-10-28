-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_8d131a4d
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_8d131a4d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:44:03.499448+00:00
-- url     : https://prove2.me/theorems/ee5fe5ac-0940-42ee-9925-9f9d4fb6a416
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on the same finite vertex set, with at least three vertices, has at least 3|V|−6 edges. This removes the augmentation and triangulation argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_8d131a4d
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P ≤ N) :
    3 * (Fintype.card V : Int) - 6 ≤ (N.edgeSet.ncard : Int) := by sorry
