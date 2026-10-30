-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_upper_bound
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:28:01.620651+00:00
-- url     : https://prove2.me/theorems/3df0f6c9-c5b8-41e7-8b09-6f22aded4b43
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every finite drawable simple graph on at least three vertices has at most 3|V|−6 edges. This child supplies the target’s upper inequality; the bound also covers disconnected graphs. A proof route is to handle components and apply Euler’s formula and face-incidence counting to planar embeddings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
