-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_3109df4d_98fd_4102_824c_39bdc30faaca
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_3109df4d_98fd_4102_824c_39bdc30faaca
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:06:40.012331+00:00
-- url     : https://prove2.me/theorems/64bf74a4-2825-4891-bd51-4961046519e2
-- title:
--   Finite maximal planar extension on the same vertex type
-- statement:
--   A planar graph on a finite ordered vertex type has a planar supergraph on that same type that is maximal under edge inclusion. The original drawing makes the set of eligible graphs nonempty, and finiteness allows selection of an edge-maximal eligible graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension_3109df4d_98fd_4102_824c_39bdc30faaca
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        ∀ u v, L.Adj u v → K.Adj u v) := by sorry
