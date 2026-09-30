-- Prove2me | Theorems.Thm_Hirsch_vertex_has_injective_target_tight_basis
-- name    : Hirsch.vertex_has_injective_target_tight_basis
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T23:05:11.757389+00:00
-- url     : https://prove2.me/theorems/e46935cf-6286-4874-a742-01cc62269b2d
-- title:
--   Every polyhedron vertex supplies an injective basis of original tight rows
-- statement:
--   At every extreme point v of an n-row real H-polyhedron in R^d, one can
--   select exactly d distinct original rows, all tight at v, whose row-evaluation
--   map is injective. No simplicity, boundedness, strict interior point, or supplied
--   basis is required. In particular this applies to nonsimple vertices with more
--   than d tight rows.
--
--   This is classical active-row basis extraction. Its role in the Polynomial
--   Hirsch workspace is to remove the previously explicit basis input from the
--   full-availability compact-star construction. The present statement itself
--   asserts neither a diameter bound nor the existence of feedback models for
--   arbitrary carriers.
-- source:
--   Classical active-row basis theorem; explicit checked application at https://github.com/jjoshua2/prove2me-work/tree/7ffa3fb3cede303c579164245f01286a49351b15

import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch
open scoped BigOperators RealInnerProductSpace

theorem Hirsch.vertex_has_injective_target_tight_basis {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      Function.Injective (fun x : EuclideanSpace ℝ (Fin d) => fun k : Fin d => ⟪a (e k), x⟫) ∧
      ∀ k, ⟪a (e k), v⟫ = b (e k) := by sorry
