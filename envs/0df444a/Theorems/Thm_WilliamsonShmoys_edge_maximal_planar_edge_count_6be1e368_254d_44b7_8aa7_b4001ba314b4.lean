-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_6be1e368_254d_44b7_8aa7_b4001ba314b4
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_6be1e368_254d_44b7_8aa7_b4001ba314b4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:20:21.537988+00:00
-- url     : https://prove2.me/theorems/bd3b5c4b-c314-41ce-8e59-29ae7620fdc1
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices with no proper drawable supergraph on the same vertex type has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_6be1e368_254d_44b7_8aa7_b4001ba314b4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
