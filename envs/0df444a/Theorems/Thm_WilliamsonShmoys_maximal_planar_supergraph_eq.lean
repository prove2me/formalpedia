-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_eq
-- name    : WilliamsonShmoys.maximal_planar_supergraph_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:40:25.182035+00:00
-- url     : https://prove2.me/theorems/3530ecc4-5ec0-4d8a-a00b-5ddb193465aa
-- title:
--   Maximality identifies a planar supergraph
-- statement:
--   If H is maximal among planar graphs on the same vertex type, then every planar supergraph J of H on that type equals H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_eq
    {V : Type} [Fintype V] [LinearOrder V]
    (H J : SimpleGraph V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → K = H)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hHJ : ∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) :
    J = H := by sorry
