-- Prove2me | Theorems.Thm_WilliamsonShmoys_not_reachable_vertices_ne
-- name    : WilliamsonShmoys.not_reachable_vertices_ne
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:32:52.716614+00:00
-- url     : https://prove2.me/theorems/1a596633-3845-4ca6-a681-7e6fd8a7f4f4
-- title:
--   Unreachable vertices are distinct
-- statement:
--   A vertex is reachable from itself, so the non-reachability hypothesis forces the endpoints to be distinct. This enables the parent’s endpoint-order case split.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.not_reachable_vertices_ne
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    u ≠ v := by sorry
