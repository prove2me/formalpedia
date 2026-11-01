-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- name    : WilliamsonShmoys.inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:51.406703+00:00
-- url     : https://prove2.me/theorems/c35528ef-9e7a-47ce-ad15-6f32623d8cca
-- title:
--   An inclusion-maximal drawable graph is connected
-- statement:
--   A drawable graph that is maximal among all drawable supergraphs on the same finite vertex type is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.Connected := by sorry
