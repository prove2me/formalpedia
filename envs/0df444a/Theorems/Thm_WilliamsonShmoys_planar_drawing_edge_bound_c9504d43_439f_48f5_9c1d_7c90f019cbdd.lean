-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_c9504d43_439f_48f5_9c1d_7c90f019cbdd
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_c9504d43_439f_48f5_9c1d_7c90f019cbdd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:30:39.672863+00:00
-- url     : https://prove2.me/theorems/25675b0b-d874-4efe-98fe-9534bdcace7e
-- title:
--   Euler edge bound for a finite crossing-free drawing
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges. This supplies the target’s upper bound. A proof route is to derive Euler’s formula for a connected drawing, handle disconnected drawings by connecting components or summing component bounds, and count face boundary incidences. The remaining work is to formalize those topological and finite-counting steps for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_c9504d43_439f_48f5_9c1d_7c90f019cbdd
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
