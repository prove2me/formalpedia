-- Prove2me | solution 2 for lean_workbook_plus_57364
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:56:52.830502+00:00
-- url     : https://prove2.me/submissions/c76d750e-6aed-4c7b-967f-435d7099d0d3

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

namespace SecondOrderProbability

section Model
variable {K : Type*} [Field K]

def state (c d : K) : ℕ → K × K
  | 0 => (c, d)
  | n + 1 => ((state c d n).2, (1 + (state c d n).2 - (state c d n).1) / 2)

def model (c d : K) (n : ℕ) : K := (state c d n).1

theorem model_zero (c d : K) : model c d 0 = c := rfl

theorem model_one (c d : K) : model c d 1 = d := rfl

theorem model_recurrence (c d : K) (n : ℕ) :
    model c d (n + 2) = (1 + model c d (n + 1) - model c d n) / 2 := rfl

theorem uniqueness (p : ℕ → K)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    p n = model (p 0) (p 1) n := by
  have h (k : ℕ) : p k = model (p 0) (p 1) k ∧
      p (k + 1) = model (p 0) (p 1) (k + 1) := by
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      change p (k + 2) = model (p 0) (p 1) (k + 2)
      rw [hp, model_recurrence, ih.1, ih.2]
  exact (h n).1

theorem exists_unique_sequence (c d : K) : ∃! p : ℕ → K,
    p 0 = c ∧ p 1 = d ∧ ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2 := by
  refine ⟨model c d, ⟨rfl, rfl, model_recurrence c d⟩, ?_⟩
  rintro p ⟨h0, h1, hp⟩
  funext n
  rw [uniqueness p hp, h0, h1]

end Model

def energy (x y : ℝ) : ℝ := x ^ 2 - x * y + 2 * y ^ 2

theorem energy_step (x y : ℝ) : energy y ((y - x) / 2) = energy x y / 2 := by
  unfold energy
  ring

theorem energy_coercive (x y : ℝ) : (7 / 8 : ℝ) * x ^ 2 ≤ energy x y := by
  unfold energy
  nlinarith only [sq_nonneg (y - x / 4)]

theorem energy_nonneg (x y : ℝ) : 0 ≤ energy x y := by
  have h := energy_coercive x y
  nlinarith only [h, sq_nonneg x]

theorem centered_recurrence (p : ℕ → ℝ)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    p (n + 2) - 1 / 2 = ((p (n + 1) - 1 / 2) - (p n - 1 / 2)) / 2 := by
  rw [hp]
  ring

theorem energy_decay (p : ℕ → ℝ)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    energy (p n - 1 / 2) (p (n + 1) - 1 / 2) =
      energy (p 0 - 1 / 2) (p 1 - 1 / 2) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change energy (p (n + 1) - 1 / 2) (p (n + 2) - 1 / 2) = _
    rw [centered_recurrence p hp n, energy_step, ih, pow_succ]
    ring

theorem squared_error_bound (p : ℕ → ℝ)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    (p n - 1 / 2) ^ 2 ≤
      (8 / 7 : ℝ) * energy (p 0 - 1 / 2) (p 1 - 1 / 2) * (1 / 2 : ℝ) ^ n := by
  have h := energy_coercive (p n - 1 / 2) (p (n + 1) - 1 / 2)
  rw [energy_decay p hp n] at h
  nlinarith only [h]

theorem absolute_error_bound (p : ℕ → ℝ)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    |p n - 1 / 2| ≤ Real.sqrt
      ((8 / 7 : ℝ) * energy (p 0 - 1 / 2) (p 1 - 1 / 2) * (1 / 2 : ℝ) ^ n) := by
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt (squared_error_bound p hp n)

theorem tendsto_half (p : ℕ → ℝ)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) :
    Tendsto p atTop (𝓝 (1 / 2)) := by
  have hg : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu := (hg.const_mul ((8 / 7 : ℝ) * energy (p 0 - 1 / 2) (p 1 - 1 / 2))).sqrt
  simp only [mul_zero, Real.sqrt_zero] at hu
  have habs := squeeze_zero (fun n => abs_nonneg (p n - 1 / 2))
    (absolute_error_bound p hp) hu
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using habs)

theorem unit_interval_invariant (p : ℕ → ℝ)
    (h0 : p 0 ∈ Set.Icc 0 1) (h1 : p 1 ∈ Set.Icc 0 1)
    (hp : ∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    p n ∈ Set.Icc 0 1 := by
  have h (k : ℕ) : p k ∈ Set.Icc 0 1 ∧ p (k + 1) ∈ Set.Icc 0 1 := by
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      change p (k + 2) ∈ Set.Icc 0 1
      rw [hp]
      constructor <;> linarith [ih.1.1, ih.1.2, ih.2.1, ih.2.2]
  exact (h n).1

theorem source_table (p : ℕ → ℚ) (h1 : p 1 = 1 / 2) (h2 : p 2 = 1 / 4)
    (hp : ∀ n, 1 ≤ n → p (n + 2) = (1 + p (n + 1) - p n) / 2) :
    p 3 = 3 / 8 ∧ p 4 = 9 / 16 ∧ p 5 = 19 / 32 ∧
      p 6 = 33 / 64 ∧ p 7 = 59 / 128 := by
  have h3 : p 3 = 3 / 8 := by linarith [hp 1 (by omega)]
  have h4 : p 4 = 9 / 16 := by linarith [hp 2 (by omega)]
  have h5 : p 5 = 19 / 32 := by linarith [hp 3 (by omega)]
  have h6 : p 6 = 33 / 64 := by linarith [hp 4 (by omega)]
  have h7 : p 7 = 59 / 128 := by linarith [hp 5 (by omega)]
  exact ⟨h3, h4, h5, h6, h7⟩

theorem source_probability (p q : ℕ → ℚ) (h1 : p 1 = 1 / 2) (h2 : p 2 = 1 / 4)
    (hp : ∀ n, 1 ≤ n → p (n + 2) = (1 + p (n + 1) - p n) / 2)
    (hq : q 7 = p 6) : (2 / 3 : ℚ) * (1 - p 7) + 1 / 3 * q 7 = 17 / 32 := by
  obtain ⟨_, _, _, h6, h7⟩ := source_table p h1 h2 hp
  rw [hq, h6, h7]
  ring

theorem source_sequence_limit (p : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → p (n + 2) = (1 + p (n + 1) - p n) / 2) :
    Tendsto p atTop (𝓝 (1 / 2)) := by
  have hs : ∀ n, p ((n + 2) + 1) = (1 + p ((n + 1) + 1) - p (n + 1)) / 2 := by
    intro n
    exact hp (n + 1) (by omega)
  have ht := tendsto_half (fun n => p (n + 1)) hs
  exact (tendsto_add_atTop_iff_nat 1).mp ht

theorem source_probability_limit (p : ℕ → ℝ)
    (hp : ∀ n, 1 ≤ n → p (n + 2) = (1 + p (n + 1) - p n) / 2) :
    Tendsto (fun n => (2 / 3 : ℝ) * (1 - p (n + 1)) + 1 / 3 * p n) atTop (𝓝 (1 / 2)) := by
  have ht := source_sequence_limit p hp
  have hs := ht.comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := ((hc.sub hs).const_mul (2 / 3 : ℝ)).add (ht.const_mul (1 / 3 : ℝ))
  norm_num at h
  exact h

theorem source_bounds (p : ℕ → ℝ) (h1 : p 1 = 1 / 2) (h2 : p 2 = 1 / 4)
    (hp : ∀ n, 1 ≤ n → p (n + 2) = (1 + p (n + 1) - p n) / 2) (n : ℕ) :
    p (n + 1) ∈ Set.Icc 0 1 := by
  apply unit_interval_invariant (fun n => p (n + 1))
  · change p 1 ∈ Set.Icc 0 1
    rw [h1]
    norm_num
  · change p 2 ∈ Set.Icc 0 1
    rw [h2]
    norm_num
  · intro k
    exact hp (k + 1) (by omega)

theorem source_exists : ∃ p q : ℕ → ℚ,
    p 1 = 1 / 2 ∧ p 2 = 1 / 4 ∧
    (∀ n, p (n + 2) = (1 + p (n + 1) - p n) / 2) ∧
    (∀ n, q (n + 1) = p n) ∧
    (2 / 3 : ℚ) * (1 - p 7) + 1 / 3 * q 7 = 17 / 32 := by
  let p : ℕ → ℚ := model 1 (1 / 2)
  let q : ℕ → ℚ := fun n => p (n - 1)
  have h1 : p 1 = 1 / 2 := rfl
  have h2 : p 2 = 1 / 4 := by
    change model (1 : ℚ) (1 / 2) 2 = 1 / 4
    rw [show (2 : ℕ) = 0 + 2 from rfl, model_recurrence, model_zero, model_one]
    ring
  have hp := model_recurrence (1 : ℚ) (1 / 2)
  have hq : ∀ n, q (n + 1) = p n := by intro n; simp only [q, Nat.add_sub_cancel]
  exact ⟨p, q, h1, h2, hp, hq,
    source_probability p q h1 h2 (fun n _ => hp n) (hq 6)⟩

end SecondOrderProbability

theorem solution (p q : ℕ → ℚ) (h₀ : p 1 = 1 / 2) (h₁ : p 2 = 1 / 4)
    (h₂ : ∀ n, p (n + 2) = 1 / 2 * p (n + 1) + 1 / 2 * (1 - p n))
    (h₃ : ∀ n, q (n + 1) = p n) (h₄ : 0 < 7) :
    (2 / 3 * (1 - p 7) + 1 / 3 * q 7) = 17 / 32 := by
  apply SecondOrderProbability.source_probability p q h₀ h₁
  · intro n _
    rw [h₂]
    ring
  · exact h₃ 6

#print axioms SecondOrderProbability.state
#print axioms SecondOrderProbability.model
#print axioms SecondOrderProbability.model_zero
#print axioms SecondOrderProbability.model_one
#print axioms SecondOrderProbability.model_recurrence
#print axioms SecondOrderProbability.uniqueness
#print axioms SecondOrderProbability.exists_unique_sequence
#print axioms SecondOrderProbability.energy
#print axioms SecondOrderProbability.energy_step
#print axioms SecondOrderProbability.energy_coercive
#print axioms SecondOrderProbability.energy_nonneg
#print axioms SecondOrderProbability.centered_recurrence
#print axioms SecondOrderProbability.energy_decay
#print axioms SecondOrderProbability.squared_error_bound
#print axioms SecondOrderProbability.absolute_error_bound
#print axioms SecondOrderProbability.tendsto_half
#print axioms SecondOrderProbability.unit_interval_invariant
#print axioms SecondOrderProbability.source_table
#print axioms SecondOrderProbability.source_probability
#print axioms SecondOrderProbability.source_sequence_limit
#print axioms SecondOrderProbability.source_probability_limit
#print axioms SecondOrderProbability.source_bounds
#print axioms SecondOrderProbability.source_exists
#print axioms solution
