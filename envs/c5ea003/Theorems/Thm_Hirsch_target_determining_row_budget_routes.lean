-- Prove2me | Theorems.Thm_Hirsch_target_determining_row_budget_routes
-- name    : Hirsch.target_determining_row_budget_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T12:29:40.257979+00:00
-- url     : https://prove2.me/theorems/a5c47f03-d2a9-41e0-bc11-89ee4e43a726
-- title:
--   Minimum-weight original target-determining row budgets and dimension-capped routes
-- statement:
--   Let a finite real hull in ambient dimension d equal its original m halfspaces, with actual extreme endpoints u,v. Derive a subset S of the original rows tight at v but missing at u, with at most d labels, whose equations together with the already shared target equations determine the target uniquely. Among all such subsets of size at most d, choose S with minimum sum of actual row-vertex-level cardinality minus one. Construct a route through actual original extreme points paying at most that selected weight. Every consecutive segment is whole, nondegenerate and IsExtreme in the original halfspace body, and every target row acquired remains tight. The same length is at most K*min(d,m-d) whenever the SELECTED rows have at most K+1 actual vertex values; no level bound is required on unselected rows. The candidate family is proved nonempty by target-active injectivity and selection from the restricted row span. No supplied basis, residual rank, determining subset, graph, short phase or route is an input premise. Exact finite H/hull equality and actual endpoints remain explicit. Redundancy, nonsimple/lower-dimensional bodies, zero dimensions and coincident endpoints are included. The general optimized weight can still be exponential, so this is not unrestricted Polynomial Hirsch or a shortest-path assertion.
-- source:
--   Compose accepted #325 small_active_rows with accepted #329 genuine original-edge acquisition phases. Restrict target-active rows to the kernel of equations already common to both endpoints, derive a small completion, minimize its finite nonnegative weight, and construct only the selected acquisition phases. All retained accepted proof bodies are reused without changes; prior public roots are not resubmitted. Classical finite-dimensional row-space selection and finite minimization, not historical priority, a new best-known general polytope bound, or a verified polynomial-time optimization algorithm. #326, #282 and reserved #210 are not modified.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.target_determining_row_budget_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let T := @Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let G := @Finset.filter (Fin m) (fun i => A i u=b i ∧ A i v=b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    ∃ S : Finset (Fin m), S ⊆ T ∧ S.card ≤ d ∧
      (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ S, A i z=0) → z=0) ∧
      ∃ L : ℕ, L ≤ ∑ i ∈ S, ((V.image (fun x => A i x)).card-1) ∧
        (∀ R : Finset (Fin m), R ⊆ T → R.card ≤ d →
          (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ R, A i z=0) → z=0) →
          (∑ i ∈ S, ((V.image (fun x => A i x)).card-1)) ≤
            ∑ i ∈ R, ((V.image (fun x => A i x)).card-1)) ∧
        (∀ K : ℕ, (∀ i ∈ S, (V.image (fun x => A i x)).card ≤ K+1) →
          L ≤ K*min d (m-d)) ∧
        ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
          (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
          ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
            IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
              (segment ℝ (p t.castSucc) (p t.succ)) ∧
            (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
