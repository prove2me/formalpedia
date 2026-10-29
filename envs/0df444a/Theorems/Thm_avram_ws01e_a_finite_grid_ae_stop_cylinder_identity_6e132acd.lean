-- Prove2me | Theorems.Thm_avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_6e132acd
-- name    : avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_6e132acd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:10:39.381255+00:00
-- url     : https://prove2.me/theorems/08bfb1bf-7120-4bc1-8da5-357da22043a8
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

theorem avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_6e132acd
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
    (hfib : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s}))
    (hXm : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); ∀ r, Measurable (X.X r)))
    (hinc : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); ∀ s, MeasurableSet ((fun ω => X.X (s + u) ω -
      X.X s ω) ⁻¹' B)))
    (hAae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ↔ ω ∈ ⋃ s ∈ grid, C s)))
    (hEae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} ↔
       ω ∈ ⋃ s ∈ grid, D s)))
    (hCpartition : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); QT A = ∑ s ∈ grid, QT (C s)))
    (hDpartition : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); QT (A ∩
      {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
      ∑ s ∈ grid, QT (D s)))
    : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ s ∈ grid,
      QT (D s) = QT (C s) * QU ((X.X u) ⁻¹' B)) := by sorry
