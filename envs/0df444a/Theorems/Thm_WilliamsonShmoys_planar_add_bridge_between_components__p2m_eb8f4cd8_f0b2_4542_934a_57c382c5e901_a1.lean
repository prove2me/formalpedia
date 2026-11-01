-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_bridge_between_components__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
-- name    : WilliamsonShmoys.planar_add_bridge_between_components__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:31:44.547445+00:00
-- url     : https://prove2.me/theorems/bb71a8e8-4f54-44cc-a603-6794a7a0cd2a
-- title:
--   Add a planar bridge between distinct components
-- statement:
--   Given a crossing-free drawing of a finite graph, adding an edge between vertices in distinct connected components admits a crossing-free drawing on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_bridge_between_components__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hdis : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
