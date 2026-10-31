-- Prove2me | Theorems.Thm_WilliamsonShmoys_join_separated_planar_parts__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2
-- name    : WilliamsonShmoys.join_separated_planar_parts__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:04:57.818496+00:00
-- url     : https://prove2.me/theorems/32d05c5b-cefc-47fd-9e95-8882d3153e81
-- title:
--   Join separated planar parts by a new edge
-- statement:
--   If a planar graph has a nontrivial vertex partition with no edges across it, it has a strictly larger planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.join_separated_planar_parts__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (A : Set V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hSep : ∀ ⦃u v : V⦄, u ∈ A → v ∉ A → ¬ M.Adj u v)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
