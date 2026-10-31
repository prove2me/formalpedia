-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_strict_supergraph_of_not_connected_with_three_vertices__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a2
-- name    : WilliamsonShmoys.exists_planar_strict_supergraph_of_not_connected_with_three_vertices__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:24:21.2258+00:00
-- url     : https://prove2.me/theorems/e7a9f78b-3e2a-455c-88a9-bda4a05abdb6
-- title:
--   A disconnected drawn graph with at least three vertices has a larger planar supergraph
-- statement:
--   Every disconnected finite graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_strict_supergraph_of_not_connected_with_three_vertices__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K) (hnot : ¬ K.Connected) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ K.edgeSet.ncard < L.edgeSet.ncard := by sorry
