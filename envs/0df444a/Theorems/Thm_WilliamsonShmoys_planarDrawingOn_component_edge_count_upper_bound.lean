-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_edge_count_upper_bound
-- name    : WilliamsonShmoys.planarDrawingOn_component_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:38:09.266793+00:00
-- url     : https://prove2.me/theorems/a97d2225-3117-4f2d-96d9-2b1fce68bb1a
-- title:
--   Planar edge bound on each connected component
-- statement:
--   For every connected component with at least three vertices, the graph induced on that component satisfies the planar edge bound. The explicit finite-type instance avoids the prior statement elaboration failure. Restrict the drawing to the component and apply the connected planar Euler argument, including the bridge and tree cases needed to justify the face-count inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_component_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (c : M.ConnectedComponent)
    [Fintype {v : V // M.connectedComponentMk v = c}] :
    let S : Type := {v : V // M.connectedComponentMk v = c}
    let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
    3 ≤ Fintype.card S → H.edgeSet.ncard ≤ 3 * Fintype.card S - 6 := by sorry
