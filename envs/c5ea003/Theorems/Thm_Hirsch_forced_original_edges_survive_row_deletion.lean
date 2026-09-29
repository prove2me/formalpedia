-- Prove2me | Theorems.Thm_Hirsch_forced_original_edges_survive_row_deletion
-- name    : Hirsch.forced_original_edges_survive_row_deletion
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-24T17:31:13.094608+00:00
-- url     : https://prove2.me/theorems/ee659ed9-1c3d-4169-acf8-f1db5af75838
-- title:
--   Forced original edges survive target-row deletion as distinct exposed line sections
-- statement:
--   For a finite original real halfspace system in arbitrary dimension and an actual target vertex, retain all target-tight rows and a chosen original-row set J. Any finite family of nondegenerate original exposed edges avoiding the target whose entire target-slack common-tight label sets lie in J has canonical lifts to the relaxed body: its intersections with their original affine lines. Each lift is exposed, contains the original edge, excludes the target, and intersects the original body in exactly that edge. The line parameterization is injective and equality of lifted carriers implies equality of original edge sets; consequently distinct geometric edges have distinct lifts. Endpoints need not survive as relaxed vertices and lifts may be unbounded rays. No polynomial carrier count, route construction or congestion bound is concluded. The condition on J is precisely the forced-label condition, not a small-load assumption. Boundedness, full dimension, a vertex catalogue and a supplied rank or exposing-functional witness are not required.
-- source:
--   Geometric continuation of accepted PR343. Reuses exact finite-margin and target-extremality helpers; derives common-active affine-line completeness by two-sided feasible perturbations and exposes the relaxed carrier by summing retained original rows. Related accepted PR165 preserves target vertices under deletion and PR168 uses parent-face budgets; neither target is resubmitted. No historical novelty claim for the classical active-face geometry.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.forced_original_edges_survive_row_deletion (d m N : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (J : Finset (Fin m)) (u w : Fin N → (Fin d → ℝ))
    (hu : ∀ t, u t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)))
    (hw : ∀ t, w t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)))
    (huv : ∀ t, u t ≠ v) (hwv : ∀ t, w t ≠ v) (huw : ∀ t, u t ≠ w t)
    (hE : ∀ t, IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
      (segment ℝ (u t) (w t)))
    (hforced : ∀ t i, A i v < b i → A i (u t) = b i →
      A i (w t) = b i → i ∈ J) :
    let P : Set (Fin d → ℝ) := {x | ∀ i, A i x ≤ b i}
    let Q : Set (Fin d → ℝ) := {x | ∀ i, A i v = b i ∨ i ∈ J → A i x ≤ b i}
    let E := fun t : Fin N => {x ∈ Q | ∃ s : ℝ, x = u t + s • (w t - u t)}
    (∀ t, IsExposed ℝ Q (E t) ∧ P ∩ E t = segment ℝ (u t) (w t) ∧
      segment ℝ (u t) (w t) ⊆ E t ∧ v ∉ E t ∧
      Function.Injective (fun s : ℝ => u t + s • (w t - u t))) ∧
    (∀ s t, E s = E t → segment ℝ (u s) (w s) = segment ℝ (u t) (w t)) ∧
    (Function.Injective (fun t => segment ℝ (u t) (w t)) → Function.Injective E) := by sorry
