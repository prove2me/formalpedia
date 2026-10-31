-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:29.386665+00:00
-- url     : https://prove2.me/theorems/eb3156e0-5c6e-45fb-84b4-4b38a1e94046
-- title:
--   A maximal drawable graph with at least three vertices is connected
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing and at least three vertices is connected. If it had distinct components, an edge could be drawn between components without crossings, contradicting maximality. The topological construction of that added arc is the main remaining mathematical obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L) : L.Connected := by sorry
