-- Prove2me | Theorems.Thm_Hirsch_normalized_slack_determining_routes
-- name    : Hirsch.normalized_slack_determining_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T17:12:17.202367+00:00
-- url     : https://prove2.me/theorems/91b72fa6-be54-4e3d-a079-f5bb4e7f050b
-- title:
--   Original-edge routes from minimum determining normalized-slack spectra
-- statement:
--   For exact finite real H/hull equality in ambient d with m original inequalities and actual extreme endpoints, supply row-specific affine denominators strictly positive at every actual vertex. Derive a small initially missing target-row completion relative to the shared equations, minimize its sum of distinct normalized-slack spectrum cardinalities minus one, and construct a genuine original-edge route of length at most that minimum. The same route satisfies K*min(d,m-d) when selected weights are at most K. All visited points are actual extreme points, every segment is whole nondegenerate IsExtreme in the original body, and every acquired target row stays tight. No common projective chart, determining subset, basis, graph, short acquisition phase or route is assumed. Exact H/hull equality, actual endpoints and denominator positivity remain explicit; no universal small-spectrum or Polynomial Hirsch conclusion follows. Redundancy, nonsimple/lower-dimensional bodies, dimension zero and coincident endpoints are included.
-- source:
--   Compose accepted original-hull improving-edge and target-lock geometry and small_completion from #332 with direct linear-fractional slack linearization and finite-spectrum descent. Select a minimum normalized-weight original determining completion and construct its full phases. #203 projective transport and #256 slack-share/contraction work are prior work, not resubmitted. The separate projective-cube all-order raw-budget barrier is written mathematics supported by exact tests, not another Lean instance theorem. No historical-priority or best-known general diameter claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.normalized_slack_determining_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (D : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (a : Fin m → ℝ)
    (hpos : ∀ i, ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
      0<a i+D i x)
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
    let w := fun i => (V.image (fun x => (b i-A i x)/(a i+D i x))).card-1
    ∃ S : Finset (Fin m), S ⊆ T ∧ S.card ≤ min d (m-d) ∧
      (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ S, A i z=0) → z=0) ∧
      ∃ L : ℕ, L ≤ ∑ i ∈ S, w i ∧
        (∀ R : Finset (Fin m), R ⊆ T → R.card ≤ d →
          (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ R, A i z=0) → z=0) →
          (∑ i ∈ S, w i) ≤ ∑ i ∈ R, w i) ∧
        (∀ K : ℕ, (∀ i ∈ S, w i ≤ K) → L ≤ K*min d (m-d)) ∧
        ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
          (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
          ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
            IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
              (segment ℝ (p t.castSucc) (p t.succ)) ∧
            (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
