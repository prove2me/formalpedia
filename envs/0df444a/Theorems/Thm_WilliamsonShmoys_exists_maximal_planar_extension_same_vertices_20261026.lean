-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_same_vertices_20261026
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_same_vertices_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:25:21.39987+00:00
-- url     : https://prove2.me/theorems/6fa6ea8a-80dc-4824-bc66-604ec44231f3
-- title:
--   Existence of a maximal planar extension on the same vertices
-- statement:
--   Every connected graph with the supplied planar drawing is contained in a same-vertex planar graph maximal under edge inclusion. The vertex set remains V, so no vertices are added. A proof route is finite maximality among simple graphs on V, using preservation of the drawing under edge deletion and planar edge insertion when a larger planar supergraph exists.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension_same_vertices_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      ∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        (∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) → J = H := by sorry
