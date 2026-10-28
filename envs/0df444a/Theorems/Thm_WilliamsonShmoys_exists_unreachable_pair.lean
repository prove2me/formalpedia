-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair
-- name    : WilliamsonShmoys.exists_unreachable_pair
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T13:13:10.743448+00:00
-- url     : https://prove2.me/theorems/531114d4-ec35-4459-afad-9fbce5238bf1
-- title:
--   Extract distinct unreachable vertices
-- statement:
--   A disconnected graph contains distinct vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hnotConnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Reachable u v := by sorry
