-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_fixed_vertex_type
-- name    : WilliamsonShmoys.planar_maximal_supergraph_fixed_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:05:48.25491+00:00
-- url     : https://prove2.me/theorems/0dbfa0f6-2eab-415b-93f2-eb60f82e8443
-- title:
--   Maximal planar supergraph on the fixed vertex type
-- statement:
--   Every planar graph on a finite ordered vertex type has a planar supergraph on that same type that is maximal among planar supergraphs under edge inclusion. This removes the finite selection argument from the parent. Prove it by considering the finite set of simple graphs on V that contain K and admit a drawing, which is nonempty because it contains K, and choosing one with the largest edge set. Any strict planar supergraph would have more edges. This argument also covers disconnected K; it does not assume arbitrary edge augmentation preserves planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph_fixed_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (K <= H) (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (∀ G : SimpleGraph V, H <= G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H)) := by sorry
