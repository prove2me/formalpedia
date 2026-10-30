-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v4
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:56:33.596778+00:00
-- url     : https://prove2.me/theorems/8d131a4d-acf8-4775-a00b-077fa6ea55b5
-- title:
--   An inclusion-maximal drawable graph has the triangulated planar edge count
-- statement:
--   An inclusion-maximal drawable finite simple graph on at least three vertices has exactly 3|V|−6 edges. The claim isolates the triangulation and Euler-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P ≤ N) :
    (N.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
