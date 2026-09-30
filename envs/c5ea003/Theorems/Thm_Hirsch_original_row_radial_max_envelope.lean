-- Prove2me | Theorems.Thm_Hirsch_original_row_radial_max_envelope
-- name    : Hirsch.original_row_radial_max_envelope
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-24T03:39:30.14099+00:00
-- url     : https://prove2.me/theorems/b14806b3-8f55-41f5-a98a-8e668394a960
-- title:
--   Original-row radial max-envelope and exact vertex retention in arbitrary dimension
-- statement:
--   For exact equality of a finite real convex hull and the original m halfspaces in arbitrary dimension, and an actual target vertex, derive a strict target exposure. Prove an exact radial epigraph representation from original rows, a positive attained original-row maximum on every normalized target-cone direction, preservation of every tight-row label at every non-target actual vertex, and injectivity of the normalized original vertex map. No supplied chart, cap, row-enumeration oracle, ray endpoint or vertex list is assumed. This is a geometric and original-input-size reformulation, not a polynomial ordinary-edge route bound or a graph-isomorphism theorem. Every original exposed edge between non-target vertices is additionally assigned an original row tight at both endpoints and slack at the target. This proves existence of a row-charge witness, not a bound on repeated charges.
-- source:
--   All-dimensional original-row interface following accepted PR340. Reuses its exact finite-margin, strict-exposure, finite-hull-support and active-kernel helpers. The prior local-only candidate is now prepared for its first complete pinned hosted gate; no local Lean compilation is claimed.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.original_row_radial_max_envelope (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = {x | ∀ i, A i x ≤ b i})
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)),
        x ≠ v → 0 < h (x - v)) ∧
      (∀ (y : Fin d → ℝ) (a : ℝ), 0 < a →
        ((∀ i, A i (v + (1 / a) • y) ≤ b i) ↔
          (∀ i, A i v = b i → A i y ≤ 0) ∧
          (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a))) ∧
      (∀ y : Fin d → ℝ, h y = 1 → (∀ i, A i v = b i → A i y ≤ 0) →
        ∃ i : Fin m, A i v < b i ∧ 0 < A i y / (b i - A i v) ∧
          (∀ j, A j v < b j →
            A j y / (b j - A j v) ≤ A i y / (b i - A i v)) ∧
          ∀ a : ℝ, 0 < a →
            ((∀ j, A j (v + (1 / a) • y) ≤ b j) ↔
              A i y / (b i - A i v) ≤ a)) ∧
      (∀ x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ,
        x ≠ v →
        let y := (1 / h (x - v)) • (x - v)
        let a := 1 / h (x - v)
        h y = 1 ∧ v + (1 / a) • y = x ∧
          (∀ i, A i x = b i ↔ A i y = a * (b i - A i v)) ∧
          (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a) ∧
          ∃ i, A i v < b i ∧ A i y / (b i - A i v) = a) ∧
      (∀ u w : Fin d → ℝ,
        u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ →
        w ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ →
        u ≠ v → w ≠ v → u ≠ w →
        IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i} (segment ℝ u w) →
        ∃ i : Fin m, A i v < b i ∧ A i u = b i ∧ A i w = b i) ∧
      Set.InjOn (fun x => (1 / h (x - v)) • (x - v))
        (({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ \ {v}) := by sorry
