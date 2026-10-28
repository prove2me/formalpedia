-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fd4411d1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_fd4411d1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:21:12.381269+00:00
-- url     : https://prove2.me/theorems/fd61aa56-e03a-4e48-89a5-5739a067da7a
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_fd4411d1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by sorry
