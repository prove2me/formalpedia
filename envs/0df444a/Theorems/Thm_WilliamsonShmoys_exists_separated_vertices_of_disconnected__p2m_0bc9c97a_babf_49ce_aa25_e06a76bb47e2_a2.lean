-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_separated_vertices_of_disconnected__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
-- name    : WilliamsonShmoys.exists_separated_vertices_of_disconnected__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:54.932107+00:00
-- url     : https://prove2.me/theorems/662709d7-a21e-40a2-a35b-6fab2acfe369
-- title:
--   Choose vertices in distinct components
-- statement:
--   A disconnected graph on the given finite vertex type, whose cardinality is at least three, has distinct vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_separated_vertices_of_disconnected__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hdisc : Not G.Connected) :
    Exists fun u : V => Exists fun v : V => And (Not (u = v)) (Not (G.Reachable u v)) := by sorry
