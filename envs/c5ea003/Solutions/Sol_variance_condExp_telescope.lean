-- Prove2me | solution 1 for variance_condExp_telescope
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:38:04.887653+00:00
-- url     : https://prove2.me/submissions/055be931-7092-4a48-82a5-be5bcc69a14f

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (F : ℕ → MeasurableSpace Ω) (hmono : Monotone F) (hle : ∀ k, F k ≤ m₀) :
    ∀ N, Var[μ[X | F N]; μ]
      = Var[μ[X | F 0]; μ]
        + ∑ k ∈ Finset.range N, μ[Var[μ[X | F (k+1)]; μ | F k]] := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    have hY : MemLp (μ[X | F (n+1)]) 2 μ := hX.condExp
    have hkey : μ[Var[μ[X | F (n+1)]; μ | F n]] + Var[μ[μ[X | F (n+1)] | F n]; μ]
        = Var[μ[X | F (n+1)]; μ] :=
      integral_condVar_add_variance_condExp (hle n) hY
    have htower : μ[μ[X | F (n+1)] | F n] =ᵐ[μ] μ[X | F n] :=
      condExp_condExp_of_le (hmono (Nat.le_succ n)) (hle (n+1))
    have htv : Var[μ[μ[X | F (n+1)] | F n]; μ] = Var[μ[X | F n]; μ] :=
      variance_congr htower
    rw [htv] at hkey
    linarith
