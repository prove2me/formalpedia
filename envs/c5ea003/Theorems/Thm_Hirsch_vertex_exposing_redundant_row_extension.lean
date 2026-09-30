-- Prove2me | Theorems.Thm_Hirsch_vertex_exposing_redundant_row_extension
-- name    : Hirsch.vertex_exposing_redundant_row_extension
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T19:47:26.980817+00:00
-- url     : https://prove2.me/theorems/0fff8924-afe0-4653-8c3c-2f4f5cd815cd
-- title:
--   A vertex-exposing redundant row preserves the polytope and endpoint separation
-- statement:
--   For a finite H-polytope, a vertex v and a distinct feasible point u with no nonzero describing row tight at both, append one nonzero inequality which is tight precisely at v among feasible points and is strict at u. All old rows and the feasible set are preserved exactly, as is endpoint separation. The new row is tight at v and hence is not neutral. Thus the graph and all old neutral normals remain unchanged, but access to the specified new row is exactly access to v. Boundedness is not required. The exposing normal is the sum of the original normals active at v.
-- source:
--   Working result for the Polynomial Hirsch mission, September 2026. Exact checked source in jjoshua2/prove2me-work, branch chatgpt/prescribed-face-rank. No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.vertex_exposing_redundant_row_extension
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) (b' : Fin (n + 1) → ℝ),
      (∀ j : Fin n, a' j.castSucc = a j ∧ b' j.castSucc = b j) ∧
      Hpoly a' b' = Hpoly a b ∧
      a' (Fin.last n) ≠ 0 ∧
      ⟪a' (Fin.last n), v⟫ = b' (Fin.last n) ∧
      ⟪a' (Fin.last n), u⟫ < b' (Fin.last n) ∧
      (∀ x ∈ Hpoly a' b', ⟪a' (Fin.last n), x⟫ = b' (Fin.last n) ↔ x = v) ∧
      (∀ j, a' j ≠ 0 → ⟪a' j, u⟫ ≠ b' j ∨ ⟪a' j, v⟫ ≠ b' j) := by sorry
