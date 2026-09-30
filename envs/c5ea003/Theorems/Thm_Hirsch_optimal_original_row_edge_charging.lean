-- Prove2me | Theorems.Thm_Hirsch_optimal_original_row_edge_charging
-- name    : Hirsch.optimal_original_row_edge_charging
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-24T13:51:11.282161+00:00
-- url     : https://prove2.me/theorems/c686867d-29b6-4c57-a9fa-59852b51c051
-- title:
--   Optimal original-row edge charging with exact forced-overload certificates
-- statement:
--   For any finite original real H-system in arbitrary dimension, an actual target vertex, and a finite family of nondegenerate exposed original edges with actual endpoints distinct from the target, derive all eligible original supporting rows and an optimal integral row assignment minimizing maximum load. Capacity k is feasible exactly when every subset J of target-slack original rows contains at most k times its cardinality many edge occurrences whose entire eligible set lies in J. Derive the least capacity K, an attaining assignment, K<=N and N<=K*|I|, and a nonempty original-row overload witness for every k<K. Edge occurrences are input, possibly repeated; no route construction, polynomial bound on K or Polynomial Hirsch conclusion is claimed. Boundedness and a vertex catalogue are not required.
-- source:
--   Classical capacitated Hall applied to original exposed-edge supporting labels derived using the exact accepted PR341 geometric helpers. Mathlib Hall theorem is reused at the existing pin. This is an exact assignment/obstruction certificate, not a new matching theorem or an assumed small-capacity routing property.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.optimal_original_row_edge_charging (d m N : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (u w : Fin N → (Fin d → ℝ))
    (hu : ∀ t, u t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hw : ∀ t, w t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (huv : ∀ t, u t ≠ v) (hwv : ∀ t, w t ≠ v) (huw : ∀ t, u t ≠ w t)
    (hE : ∀ t, IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
      (segment ℝ (u t) (w t))) :
    let I := @Finset.filter (Fin m) (fun i => A i v < b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let S := fun t : Fin N => @Finset.filter (Fin m)
      (fun i => A i v < b i ∧ A i (u t) = b i ∧ A i (w t) = b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let F := fun J : Finset (Fin m) => @Finset.filter (Fin N) (fun t => S t ⊆ J)
      (fun _ => Classical.propDecidable _) Finset.univ
    let Cap := fun k : ℕ => ∃ f : Fin N → Fin m, (∀ t, f t ∈ S t) ∧
      ∀ i : Fin m, (@Finset.filter (Fin N) (fun t => f t = i)
        (fun _ => Classical.propDecidable _) Finset.univ).card ≤ k
    ∃ K : ℕ, K ≤ N ∧ N ≤ K * I.card ∧ Cap K ∧
      (∀ k : ℕ, Cap k ↔ K ≤ k) ∧
      (∀ k : ℕ, Cap k ↔ ∀ J ⊆ I, (F J).card ≤ k * J.card) ∧
      (∀ k : ℕ, k < K → ∃ J : Finset (Fin m), J ⊆ I ∧ J.Nonempty ∧
        k * J.card < (F J).card ∧ (F J).card ≤ K * J.card) := by sorry
