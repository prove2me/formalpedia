-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_euler_20261028
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_euler_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:08:29.768849+00:00
-- url     : https://prove2.me/theorems/02050172-c3dd-4a8f-88fb-a04b0ff85c69
-- title:
--   Connect a drawn graph by planar augmentation
-- statement:
--   A finite graph on at least three vertices with a drawing satisfying `HasPlanarDrawingOn` has a connected supergraph on the same vertex type with such a drawing. The size hypothesis rules out the empty-type boundary case for connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_euler_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
