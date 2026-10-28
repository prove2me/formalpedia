-- Prove2me | Theorems.Thm_WilliamsonShmoys_extend_planar_drawing_connected
-- name    : WilliamsonShmoys.extend_planar_drawing_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:20:38.51076+00:00
-- url     : https://prove2.me/theorems/0d4a6d7b-90e1-495d-a46f-0d551e495794
-- title:
--   Connect a finite planar drawing without losing edges
-- statement:
--   For a finite graph on at least three vertices, extend its crossing-free drawing to a connected crossing-free graph on the same vertices, without decreasing the edge count. This separates the disconnected-component issue from the Euler bound. A proof route is to join components one at a time by arcs in a common face of the current embedding, preserving the existing drawing and adding edges; finiteness ensures that the process terminates. The lower bound on the vertex count excludes the empty-vertex obstruction to connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.extend_planar_drawing_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
