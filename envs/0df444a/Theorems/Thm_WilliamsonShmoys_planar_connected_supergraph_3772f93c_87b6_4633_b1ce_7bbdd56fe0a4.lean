-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- name    : WilliamsonShmoys.planar_connected_supergraph_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T03:08:54.259115+00:00
-- url     : https://prove2.me/theorems/e4cdda88-791e-46f6-ad35-dddc4416a633
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   Extend the graph to a connected graph on the same finite vertex type while preserving a drawing of the specified kind and adding no vertices. The proof route is to connect components with arcs in the complement of the embedded graph; the empty and already connected cases should be handled directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
