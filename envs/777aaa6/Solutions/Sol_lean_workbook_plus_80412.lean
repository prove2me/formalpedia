-- Prove2me | solution 1 for lean_workbook_plus_80412
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:04:26.71736+00:00
-- url     : https://prove2.me/submissions/6d00e9be-2eba-453c-b221-59961a95a4f8

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

namespace ThirdOrderConjugateRoot

section Model
variable {K : Type*} [Ring K]

def state (c d e : K) : ℕ → K × K × K
  | 0 => (c, d, e)
  | n + 1 => ((state c d e n).2.1, (state c d e n).2.2,
      8 * (state c d e n).2.2 - 8 * (state c d e n).2.1 + (state c d e n).1)

def model (c d e : K) (n : ℕ) : K := (state c d e n).1

theorem model_zero (c d e : K) : model c d e 0 = c := rfl
theorem model_one (c d e : K) : model c d e 1 = d := rfl
theorem model_two (c d e : K) : model c d e 2 = e := rfl

theorem model_recurrence (c d e : K) (n : ℕ) :
    model c d e (n + 3) = 8 * model c d e (n + 2) -
      8 * model c d e (n + 1) + model c d e n := rfl

theorem recurrence_unique (p q : ℕ → K)
    (hp : ∀ n, p (n + 3) = 8 * p (n + 2) - 8 * p (n + 1) + p n)
    (hq : ∀ n, q (n + 3) = 8 * q (n + 2) - 8 * q (n + 1) + q n)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) (n : ℕ) : p n = q n := by
  have h (k : ℕ) : p k = q k ∧ p (k + 1) = q (k + 1) ∧ p (k + 2) = q (k + 2) := by
    induction k with
    | zero => exact ⟨h0, h1, h2⟩
    | succ k ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      change p (k + 3) = q (k + 3)
      rw [hp, hq, ih.1, ih.2.1, ih.2.2]
  exact (h n).1

theorem uniqueness (p : ℕ → K)
    (hp : ∀ n, p (n + 3) = 8 * p (n + 2) - 8 * p (n + 1) + p n) (n : ℕ) :
    p n = model (p 0) (p 1) (p 2) n :=
  recurrence_unique p _ hp (model_recurrence _ _ _) rfl rfl rfl n

theorem exists_unique_sequence (c d e : K) : ∃! p : ℕ → K,
    p 0 = c ∧ p 1 = d ∧ p 2 = e ∧
      ∀ n, p (n + 3) = 8 * p (n + 2) - 8 * p (n + 1) + p n := by
  refine ⟨model c d e, ⟨rfl, rfl, rfl, model_recurrence c d e⟩, ?_⟩
  rintro p ⟨h0, h1, h2, hp⟩
  funext n
  rw [uniqueness p hp, h0, h1, h2]

theorem positive_index_model (p : ℕ → K)
    (hp : ∀ n, 1 ≤ n → p (n + 3) = 8 * p (n + 2) - 8 * p (n + 1) + p n)
    {n : ℕ} (hn : 1 ≤ n) : p n = model (p 1) (p 2) (p 3) (n - 1) := by
  have h := uniqueness (fun k => p (k + 1)) (fun k => hp (k + 1) (by omega)) (n - 1)
  simpa only [Nat.sub_add_cancel hn] using h

end Model

noncomputable def rho : ℝ := (7 + 3 * Real.sqrt 5) / 2
noncomputable def sigma : ℝ := (7 - 3 * Real.sqrt 5) / 2
noncomputable def rootSum (n : ℕ) : ℝ := rho ^ n + sigma ^ n
noncomputable def formula (n : ℕ) : ℝ := (133 + 16 * rootSum n) / 5

theorem root_sum : rho + sigma = 7 := by unfold rho sigma; ring

theorem root_product : rho * sigma = 1 := by
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold rho sigma
  nlinarith only [h]

theorem root_squares : rho ^ 2 = 7 * rho - 1 ∧ sigma ^ 2 = 7 * sigma - 1 := by
  constructor
  · calc
      rho ^ 2 = rho * (rho + sigma) - rho * sigma := by ring
      _ = 7 * rho - 1 := by rw [root_sum, root_product]; ring
  · calc
      sigma ^ 2 = sigma * (rho + sigma) - rho * sigma := by ring
      _ = 7 * sigma - 1 := by rw [root_sum, root_product]; ring

theorem rootSum_recurrence (n : ℕ) : rootSum (n + 2) = 7 * rootSum (n + 1) - rootSum n := by
  unfold rootSum
  rw [pow_add, pow_add, root_squares.1, root_squares.2, pow_succ, pow_succ]
  ring

theorem rootSum_initial : rootSum 0 = 2 ∧ rootSum 1 = 7 ∧ rootSum 2 = 47 := by
  have h0 : rootSum 0 = 2 := by unfold rootSum; ring
  have h1 : rootSum 1 = 7 := by simpa only [rootSum, pow_one] using root_sum
  have h2 := rootSum_recurrence 0
  simp only [zero_add, h0, h1] at h2
  exact ⟨h0, h1, by linarith⟩

theorem formula_initial : formula 0 = 33 ∧ formula 1 = 49 ∧ formula 2 = 177 := by
  unfold formula
  rw [rootSum_initial.1, rootSum_initial.2.1, rootSum_initial.2.2]
  constructor
  · ring
  constructor <;> ring

theorem formula_recurrence (n : ℕ) :
    formula (n + 3) = 8 * formula (n + 2) - 8 * formula (n + 1) + formula n := by
  have h := rootSum_recurrence n
  have h' := rootSum_recurrence (n + 1)
  unfold formula
  change rootSum (n + 3) = 7 * rootSum (n + 2) - rootSum (n + 1) at h'
  linarith

theorem real_closed_form (p : ℕ → ℝ) (h0 : p 0 = 33) (h1 : p 1 = 49) (h2 : p 2 = 177)
    (hp : ∀ n, p (n + 3) = 8 * p (n + 2) - 8 * p (n + 1) + p n) (n : ℕ) :
    p n = formula n :=
  recurrence_unique p formula hp formula_recurrence
    (h0.trans formula_initial.1.symm) (h1.trans formula_initial.2.1.symm)
    (h2.trans formula_initial.2.2.symm) n

theorem integer_model_formula (n : ℕ) : ((model (33 : ℤ) 49 177 n : ℤ) : ℝ) = formula n := by
  apply real_closed_form (fun k => ((model (33 : ℤ) 49 177 k : ℤ) : ℝ))
  · simp only [model_zero, Int.cast_ofNat]
  · simp only [model_one, Int.cast_ofNat]
  · simp only [model_two, Int.cast_ofNat]
  · intro k
    rw [model_recurrence]
    push_cast
    rfl

theorem formula_integral (n : ℕ) : ∃ z : ℤ, (z : ℝ) = formula n :=
  ⟨model 33 49 177 n, integer_model_formula n⟩

theorem source_closed_form (a : ℕ → ℤ) (h1 : a 1 = 33) (h2 : a 2 = 49) (h3 : a 3 = 177)
    (ha : ∀ n, 1 ≤ n → a (n + 3) = 8 * a (n + 2) - 8 * a (n + 1) + a n)
    {n : ℕ} (hn : 1 ≤ n) : (a n : ℝ) =
      (133 + 16 * (((7 + 3 * Real.sqrt 5) / 2) ^ (n - 1) +
        ((7 - 3 * Real.sqrt 5) / 2) ^ (n - 1))) / 5 := by
  rw [positive_index_model a ha hn, h1, h2, h3, integer_model_formula]
  rfl

theorem source_exists : ∃ a : ℕ → ℤ,
    a 1 = 33 ∧ a 2 = 49 ∧ a 3 = 177 ∧
      ∀ n, 1 ≤ n → a (n + 3) = 8 * a (n + 2) - 8 * a (n + 1) + a n := by
  refine ⟨fun n => model 33 49 177 (n - 1), rfl, rfl, rfl, ?_⟩
  intro n hn
  have h := model_recurrence (33 : ℤ) 49 177 (n - 1)
  change model (33 : ℤ) 49 177 (n + 3 - 1) =
    8 * model 33 49 177 (n + 2 - 1) - 8 * model 33 49 177 (n + 1 - 1) + model 33 49 177 (n - 1)
  simpa only [show n + 3 - 1 = n - 1 + 3 by omega,
    show n + 2 - 1 = n - 1 + 2 by omega,
    show n + 1 - 1 = n - 1 + 1 by omega] using h

theorem root_bounds : 1 < rho ∧ 0 < sigma ∧ sigma < 1 := by
  have hr : 1 < rho := by unfold rho; nlinarith only [Real.sqrt_nonneg 5]
  have hs : sigma = 1 / rho := by
    apply (eq_div_iff (ne_of_gt (lt_trans zero_lt_one hr))).2
    simpa only [mul_comm] using root_product
  rw [hs]
  exact ⟨hr, div_pos zero_lt_one (lt_trans zero_lt_one hr),
    (div_lt_one (lt_trans zero_lt_one hr)).2 hr⟩

theorem scaled_formula (n : ℕ) :
    sigma ^ n * formula n = (133 * sigma ^ n + 16 + 16 * (sigma ^ 2) ^ n) / 5 := by
  have hp : sigma ^ n * rho ^ n = 1 := by rw [← mul_pow, mul_comm sigma rho, root_product, one_pow]
  have hs : (sigma ^ 2) ^ n = sigma ^ n * sigma ^ n := by rw [← mul_pow]; congr 1; ring
  unfold formula rootSum
  rw [hs]
  calc
    sigma ^ n * ((133 + 16 * (rho ^ n + sigma ^ n)) / 5) =
        (133 * sigma ^ n + 16 * (sigma ^ n * rho ^ n) +
          16 * (sigma ^ n * sigma ^ n)) / 5 := by ring
    _ = _ := by rw [hp]; ring

theorem scaled_limit : Tendsto (fun n : ℕ => sigma ^ n * formula n) atTop (𝓝 (16 / 5)) := by
  have hs : Tendsto (fun n : ℕ => sigma ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one root_bounds.2.1.le root_bounds.2.2
  have hsq : Tendsto (fun n : ℕ => (sigma ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) (by nlinarith [root_bounds.2.1, root_bounds.2.2])
  have h := (((hs.const_mul 133).add_const 16).add (hsq.const_mul 16)).div_const 5
  simpa only [scaled_formula, mul_zero, add_zero, zero_add] using h

theorem source_scaled_limit (a : ℕ → ℤ) (h1 : a 1 = 33) (h2 : a 2 = 49) (h3 : a 3 = 177)
    (ha : ∀ n, 1 ≤ n → a (n + 3) = 8 * a (n + 2) - 8 * a (n + 1) + a n) :
    Tendsto (fun n : ℕ => sigma ^ n * (a (n + 1) : ℝ)) atTop (𝓝 (16 / 5)) := by
  convert scaled_limit using 1
  funext n
  rw [positive_index_model a ha (by omega : 1 ≤ n + 1), h1, h2, h3]
  simp only [Nat.add_sub_cancel, integer_model_formula]

end ThirdOrderConjugateRoot

theorem solution (a : ℕ → ℤ) (a1 : a 0 = 33) (a2 : a 1 = 49) (a3 : a 2 = 177)
    (a_rec : ∀ n, n ≥ 1 → a (n + 3) = 8 * a (n + 2) - 8 * a (n + 1) + a n) :
    ∃ f : ℕ → ℤ, ∀ n, n ≥ 1 → a n = f n := by
  refine ⟨fun n => ThirdOrderConjugateRoot.model 49 177 (a 3) (n - 1), ?_⟩
  intro n hn
  rw [ThirdOrderConjugateRoot.positive_index_model a a_rec hn, a2, a3]

#print axioms ThirdOrderConjugateRoot.state
#print axioms ThirdOrderConjugateRoot.model
#print axioms ThirdOrderConjugateRoot.model_zero
#print axioms ThirdOrderConjugateRoot.model_one
#print axioms ThirdOrderConjugateRoot.model_two
#print axioms ThirdOrderConjugateRoot.model_recurrence
#print axioms ThirdOrderConjugateRoot.recurrence_unique
#print axioms ThirdOrderConjugateRoot.uniqueness
#print axioms ThirdOrderConjugateRoot.exists_unique_sequence
#print axioms ThirdOrderConjugateRoot.positive_index_model
#print axioms ThirdOrderConjugateRoot.rho
#print axioms ThirdOrderConjugateRoot.sigma
#print axioms ThirdOrderConjugateRoot.rootSum
#print axioms ThirdOrderConjugateRoot.formula
#print axioms ThirdOrderConjugateRoot.root_sum
#print axioms ThirdOrderConjugateRoot.root_product
#print axioms ThirdOrderConjugateRoot.root_squares
#print axioms ThirdOrderConjugateRoot.rootSum_recurrence
#print axioms ThirdOrderConjugateRoot.rootSum_initial
#print axioms ThirdOrderConjugateRoot.formula_initial
#print axioms ThirdOrderConjugateRoot.formula_recurrence
#print axioms ThirdOrderConjugateRoot.real_closed_form
#print axioms ThirdOrderConjugateRoot.integer_model_formula
#print axioms ThirdOrderConjugateRoot.formula_integral
#print axioms ThirdOrderConjugateRoot.source_closed_form
#print axioms ThirdOrderConjugateRoot.source_exists
#print axioms ThirdOrderConjugateRoot.root_bounds
#print axioms ThirdOrderConjugateRoot.scaled_formula
#print axioms ThirdOrderConjugateRoot.scaled_limit
#print axioms ThirdOrderConjugateRoot.source_scaled_limit
#print axioms solution
