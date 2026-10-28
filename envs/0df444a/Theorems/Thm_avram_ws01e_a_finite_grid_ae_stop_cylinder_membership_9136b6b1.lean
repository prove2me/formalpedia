-- Prove2me | Theorems.Thm_avram_ws01e_a_finite_grid_ae_stop_cylinder_membership_9136b6b1
-- name    : avram_ws01e_a_finite_grid_ae_stop_cylinder_membership_9136b6b1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:05:40.706302+00:00
-- url     : https://prove2.me/theorems/de4bd8c0-f29a-4d1e-9edd-5ca4163b6eed
-- title:
--   Avram ws01e a finite grid ae stop cylinder: Membership result
-- statement:
--   The indicated mathematical object belongs to the stated set under the theorem's assumptions.

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem avram_ws01e_a_finite_grid_ae_stop_cylinder_membership_9136b6b1
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
    : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} ↔
       ω ∈ ⋃ s ∈ grid, D s)) := by sorry
