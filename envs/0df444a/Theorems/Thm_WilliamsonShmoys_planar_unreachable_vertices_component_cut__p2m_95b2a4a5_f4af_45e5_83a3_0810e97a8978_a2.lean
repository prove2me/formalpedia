-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_unreachable_vertices_component_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
-- name    : WilliamsonShmoys.planar_unreachable_vertices_component_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:11.411796+00:00
-- url     : https://prove2.me/theorems/5eb5d5a8-5893-495b-8592-f874d414a07f
-- title:
--   Unreachable vertices determine an edge-free component cut
-- statement:
--   If `a` cannot reach `b`, there is a set of vertices containing `a` but not `b` such that every edge has both endpoints in the set or both outside it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_unreachable_vertices_component_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (a b : V) (hnotReach : ¬ K.Reachable a b) :
    ∃ P : Set V, P a ∧ ¬ P b ∧
      ∀ u v, K.Adj u v → (P u ↔ P v) := by sorry
