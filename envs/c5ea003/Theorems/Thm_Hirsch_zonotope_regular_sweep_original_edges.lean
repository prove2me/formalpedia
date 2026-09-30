-- Prove2me | Theorems.Thm_Hirsch_zonotope_regular_sweep_original_edges
-- name    : Hirsch.zonotope_regular_sweep_original_edges
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T18:36:51.677464+00:00
-- url     : https://prove2.me/theorems/4713ca26-d458-47e6-9ae0-4654b0322f39
-- title:
--   Construct a regular objective sweep with at most m original zonotope edge faces
-- statement:
--   For arbitrary real generators w_i and two linear objectives f,g nonzero on every nonzero generator, construct a regularized target k with exactly the same generator signs and the same whole maximizing face as g. The straight objective segment from f to k has an exactly characterized finite set T of nonzero-generator ties, entirely in (0,1), of cardinality at most m. Every time in T exposes a whole nondegenerate original edge of the segment sum, with exposed/extreme face status and actual extreme endpoints. At every other time in [0,1], the whole maximizing face is a singleton actual extreme point. The perturbation, avoidance of independent simultaneous ties, exceptional set and face geometry are conclusions, not supplied genericity or adjacency hypotheses. Zero, parallel, opposite, repeated and rank-deficient generators are retained. This does not yet assemble the ordered crossings into a vertex walk or supply regular endpoint objectives for arbitrary actual vertices. m counts generators, not original H facets; no unrestricted Polynomial Hirsch bound is asserted.
-- source:
--   Distinct regular-objective sweep obligation after accepted PR312, theorem bb32ac53-d8ba-4e21-92eb-b7e5ec568c70. Its entire 425-line namespace prefix is reused byte-for-byte, omitting the old public root/prints. The generic functional is derived with pinned Mathlib Module.exists_dual_forall_apply_ne_zero, not an assumed oracle; finite-margin proof is reused from the accepted geometry chain. Classical zonotope/hyperplane-arrangement viewpoint is credited, e.g. Deza and Pournin, A linear optimization oracle for zonotope computation, arXiv:1912.02439. No historical novelty is claimed.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_regular_sweep_original_edges (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    let F : ((Fin d → ℝ) →ₗ[ℝ] ℝ) → Set (Fin d → ℝ) :=
      fun h => {x | x ∈ Z ∧ h x = ∑ i : Fin m, max 0 (h (w i))}
    ∃ k : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∃ T : Finset ℝ,
      (∀ i, (0 < k (w i) ↔ 0 < g (w i)) ∧ (w i ≠ 0 → k (w i) ≠ 0)) ∧
      F k = F g ∧ T.card ≤ m ∧
      (∀ t, t ∈ T ↔ 0 < t ∧ t < 1 ∧
        ∃ i, w i ≠ 0 ∧ ((1-t) • f + t • k) (w i)=0) ∧
      (∀ t ∈ T, ∃ u v : Fin d → ℝ, u ≠ v ∧ F ((1-t) • f + t • k)=segment ℝ u v ∧
        IsExposed ℝ Z (segment ℝ u v) ∧ IsExtreme ℝ Z (segment ℝ u v) ∧
        u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ) ∧
      (∀ t, 0 ≤ t → t ≤ 1 → t ∉ T →
        ∃ u ∈ Z.extremePoints ℝ, F ((1-t) • f + t • k)={u}) := by sorry
