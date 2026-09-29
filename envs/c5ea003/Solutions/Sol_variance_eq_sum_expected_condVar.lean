-- Prove2me | solution 1 for variance_eq_sum_expected_condVar
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:38:05.263294+00:00
-- url     : https://prove2.me/submissions/2107e5a9-f3a5-4ad4-ac61-84e836fc1e7d

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (F : ℕ → MeasurableSpace Ω) (hmono : Monotone F) (hle : ∀ k, F k ≤ m₀)
    (hbot : F 0 = ⊥) (N : ℕ) (htop : F N = m₀) :
    Var[X; μ]
      = ∑ k ∈ Finset.range N, μ[Var[μ[X | F (k+1)]; μ | F k]] := by
  -- Doob telescoping over the filtration (general in M, independent of htop)
  have htelgen : ∀ M, Var[μ[X | F M]; μ]
      = Var[μ[X | F 0]; μ]
        + ∑ k ∈ Finset.range M, μ[Var[μ[X | F (k+1)]; μ | F k]] := by
    intro M
    induction M with
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
  have htel := htelgen N
  -- bottom term: Var(E[X | ⊥]) = Var(const ∫X) = 0
  have hbot0 : Var[μ[X | F 0]; μ] = 0 := by
    rw [hbot, condExp_bot X]
    have : Var[(fun _ : Ω => ∫ x, X x ∂μ); μ]
        = Var[fun ω : Ω => (∫ x, X x ∂μ) + (fun _ : Ω => (0 : ℝ)) ω; μ] := by
      simp
    rw [this, variance_const_add (aestronglyMeasurable_const) (∫ x, X x ∂μ)]
    exact variance_zero μ
  -- top term: E[X | m₀] =ᵐ X  ⇒  Var(E[X | F N]) = Var(X)
  have hXm : AEStronglyMeasurable[m₀] X μ := hX.aestronglyMeasurable
  have htopae : μ[X | F N] =ᵐ[μ] X := by
    rw [htop]
    exact condExp_of_aestronglyMeasurable' le_rfl hXm (hX.integrable one_le_two)
  have htopvar : Var[μ[X | F N]; μ] = Var[X; μ] := variance_congr htopae
  rw [htopvar, hbot0, zero_add] at htel
  exact htel
