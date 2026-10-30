-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_arc_in_path_range__p2m_fbc04312_9eeb_4654_891c_ce7d8210aa33_a2
-- name    : WilliamsonShmoys.exists_arc_in_path_range__p2m_fbc04312_9eeb_4654_891c_ce7d8210aa33_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:05.930996+00:00
-- url     : https://prove2.me/theorems/e0135482-0414-4017-add7-8bfaedc22585
-- title:
--   Extract an injective arc from a path image
-- statement:
--   For a path in a metric space with distinct endpoints, its image contains a continuous injective arc with the same endpoints, parametrized on `[0,1]`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open unitInterval
set_option autoImplicit false

theorem WilliamsonShmoys.exists_arc_in_path_range__p2m_fbc04312_9eeb_4654_891c_ce7d8210aa33_a2 {X : Type} [MetricSpace X] {x y : X} (p : Path x y) (hxy : x ≠ y) : ∃ γ : ℝ → X, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ Set.range (fun s : I => p s) := by sorry
