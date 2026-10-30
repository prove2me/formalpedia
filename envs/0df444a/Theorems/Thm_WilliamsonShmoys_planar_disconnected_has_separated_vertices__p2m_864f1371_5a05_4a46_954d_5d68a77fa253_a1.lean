-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1
-- name    : WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:14.662242+00:00
-- url     : https://prove2.me/theorems/121e690a-13c8-451b-819b-97cd09acef9e
-- title:
--   A disconnected graph has vertices in distinct components
-- statement:
--   A finite disconnected graph has two distinct vertices that are not connected by a path. This separates endpoint selection from the planar drawing construction; a proof follows from the connectedness and reachability definitions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdisc : ¬ H.Connected) : ∃ u : V, ∃ v : V, u ≠ v ∧ ¬ H.Reachable u v := by sorry
