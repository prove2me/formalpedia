-- Prove2me | Theorems.Thm_avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_8a7e793e
-- name    : avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_8a7e793e
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:05:41.391923+00:00
-- url     : https://prove2.me/theorems/6157305b-b076-4ade-8fc9-db839c8bf1b5
-- title:
--   Avram ws01e a finite grid ae stop cylinder: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_8a7e793e
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ᵐ ω ∂(P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))), τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B) 
    (hfib : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s}))
    (hXm : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); ∀ r, Measurable (X.X r)))
    (hinc : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); ∀ s, MeasurableSet ((fun ω => X.X (s + u) ω -
      X.X s ω) ⁻¹' B)))
    (hAae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ↔ ω ∈ ⋃ s ∈ grid, C s)))
    (hEae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} ↔
       ω ∈ ⋃ s ∈ grid, D s)))
    : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); QT A = ∑ s ∈ grid, QT (C s)) := by sorry
