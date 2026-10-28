-- Prove2me | Theorems.Thm_WilliamsonShmoys_walks_mono_of_adj_inclusion
-- name    : WilliamsonShmoys.walks_mono_of_adj_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:23:04.920794+00:00
-- url     : https://prove2.me/theorems/fa48b8de-f311-4dd7-8c30-c72681c787eb
-- title:
--   Walks persist under edge inclusion
-- statement:
--   If every edge of one simple graph is an edge of another on the same vertices, every walk in the first graph is a walk in the second.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.walks_mono_of_adj_inclusion
    {V : Type} {G H : SimpleGraph V}
    (hGH : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v)
    {u v : V} (hwalk : Nonempty (G.Walk u v)) :
    Nonempty (H.Walk u v) := by sorry
