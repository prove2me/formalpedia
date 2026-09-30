-- Prove2me | solution 1 for lean_workbook_plus_64941
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:21:14.99929+00:00
-- url     : https://prove2.me/submissions/d6693572-f0f4-4633-8bc9-d8b4ed6c1b18

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace TelescopingRatioRecurrence

section Field
variable {K : Type*} [Field K] [CharZero K]

def term (c : K) (n : ℕ) : K := 2 * c / (((n : K) + 1) * ((n : K) + 2))

theorem positive_cast_ne_zero (n k : ℕ) (hk : 0 < k) : (n : K) + k ≠ 0 := by
  exact_mod_cast (show n + k ≠ 0 by omega)

theorem term_zero (c : K) : term c 0 = c := by
  norm_num [term]

theorem term_step (c : K) (n : ℕ) :
    ((n : K) + 1) * term c n = ((n : K) + 3) * term c (n + 1) := by
  have h1 := positive_cast_ne_zero (K := K) n 1 (by omega)
  have h2 := positive_cast_ne_zero (K := K) n 2 (by omega)
  have h3 := positive_cast_ne_zero (K := K) n 3 (by omega)
  norm_num at h1 h2 h3
  simp only [term, Nat.cast_add, Nat.cast_one]
  convert (show ((n : K) + 1) * (2 * c / (((n : K) + 1) * ((n : K) + 2))) =
      ((n : K) + 3) * (2 * c / (((n : K) + 2) * ((n : K) + 3))) by
    field_simp [h1, h2, h3]) using 1
  ring

def Source (c : K) (a : ℕ → K) : Prop :=
  a 1 = c ∧ ∀ n : ℕ, 2 ≤ n → ((n : K) - 1) * a (n - 1) = ((n : K) + 1) * a n

omit [CharZero K] in
theorem source_step (c : K) (a : ℕ → K) (ha : Source c a) (n : ℕ) :
    ((n : K) + 1) * a (n + 1) = ((n : K) + 3) * a (n + 2) := by
  convert ha.2 (n + 2) (by omega) using 1 <;> push_cast <;> ring

theorem source_unique (c : K) (a : ℕ → K) (ha : Source c a) :
    ∀ n : ℕ, a (n + 1) = term c n := by
  intro n
  induction n with
  | zero => simpa [term_zero] using ha.1
  | succ n ih =>
    apply mul_left_cancel₀ (positive_cast_ne_zero (K := K) n 3 (by omega))
    have hs := source_step c a ha n
    rw [ih, term_step] at hs
    exact hs.symm

def model (c z : K) : ℕ → K
  | 0 => z
  | n + 1 => term c n

theorem model_source (c z : K) : Source c (model c z) := by
  refine ⟨term_zero c, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simpa only [Nat.add_sub_cancel, model, Nat.cast_add, Nat.cast_ofNat,
    add_sub_cancel_right, show (k : K) + 2 - 1 = k + 1 by ring,
    show (k : K) + 2 + 1 = k + 3 by ring] using term_step c k

theorem model_classification (c z : K) (a : ℕ → K) :
    (a 0 = z ∧ Source c a) ↔ a = model c z := by
  constructor
  · rintro ⟨h0, hs⟩
    funext n
    cases n with
    | zero => exact h0
    | succ n => exact source_unique c a hs n
  · rintro rfl
    exact ⟨rfl, model_source c z⟩

theorem positive_index_formula (c : K) (a : ℕ → K) (ha : Source c a)
    (n : ℕ) (hn : 0 < n) : a n = 2 * c / ((n : K) * ((n : K) + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [source_unique c a ha k]
  simp only [term, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

theorem source_exists (c z : K) : ∃ a : ℕ → K, a 0 = z ∧ Source c a :=
  ⟨model c z, rfl, model_source c z⟩

theorem source_iff_formula (c : K) (a : ℕ → K) :
    Source c a ↔ ∀ n : ℕ, 0 < n → a n = 2 * c / ((n : K) * ((n : K) + 1)) := by
  constructor
  · exact positive_index_formula c a
  · intro h
    have he : a = model c (a 0) := by
      funext n
      cases n with
      | zero => rfl
      | succ n =>
        rw [h (n + 1) (by omega), model]
        simp only [term, Nat.cast_add, Nat.cast_one]
        congr 2
        ring
    rw [he]
    exact model_source c (a 0)

theorem source_answer (a : ℕ → K) (ha : Source (1 / 2) a)
    (n : ℕ) (hn : 0 < n) : a n = 1 / ((n : K) * ((n : K) + 1)) := by
  simpa using positive_index_formula (1 / 2) a ha n hn

end Field

theorem term_positive (c : ℝ) (hc : 0 < c) (n : ℕ) : 0 < term c n := by
  unfold term
  positivity

theorem term_strict_decrease (c : ℝ) (hc : 0 < c) (n : ℕ) : term c (n + 1) < term c n := by
  have hp := term_positive c hc (n + 1)
  have hs := term_step c n
  have hn : (0 : ℝ) < n + 1 := by positivity
  nlinarith

theorem term_reciprocal_bound (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ term c n ∧ term c n ≤ 2 * c / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  constructor
  · unfold term
    positivity
  · apply (div_le_div_iff₀ (mul_pos hn hn2) hn).mpr
    have hcn : 0 ≤ c * ((n : ℝ) + 1) := mul_nonneg hc hn.le
    nlinarith

theorem term_tendsto_zero (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (term c) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => 2 * c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := 2 * c)).mul hd.inv_tendsto_atTop
  exact squeeze_zero (fun n => (term_reciprocal_bound c hc n).1)
    (fun n => (term_reciprocal_bound c hc n).2) hb

theorem source_positive_decay (a : ℕ → ℝ) (ha : Source (1 / 2) a) :
    (∀ n, 0 < a (n + 1)) ∧ (∀ n, a (n + 2) < a (n + 1)) ∧
      Tendsto (fun n => a (n + 1)) atTop (𝓝 0) := by
  have he : (fun n => a (n + 1)) = term (1 / 2 : ℝ) := funext (source_unique _ a ha)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [source_unique _ a ha n]
    exact term_positive _ (by norm_num) n
  · intro n
    rw [source_unique _ a ha (n + 1), source_unique _ a ha n]
    exact term_strict_decrease _ (by norm_num) n
  · rw [he]
    exact term_tendsto_zero _ (by norm_num)

end TelescopingRatioRecurrence

theorem solution (n : ℕ) (a : ℕ → ℚ) (a1 : a 0 = 1 / 2)
    (a_rec : ∀ n, (n - 1) * a (n - 1) = (n + 1) * a n) :
    a n = 1 / (n * (n + 1)) := by
  have h := a_rec 0
  norm_num [a1] at h

#print axioms TelescopingRatioRecurrence.term
#print axioms TelescopingRatioRecurrence.positive_cast_ne_zero
#print axioms TelescopingRatioRecurrence.term_zero
#print axioms TelescopingRatioRecurrence.term_step
#print axioms TelescopingRatioRecurrence.Source
#print axioms TelescopingRatioRecurrence.source_step
#print axioms TelescopingRatioRecurrence.source_unique
#print axioms TelescopingRatioRecurrence.model
#print axioms TelescopingRatioRecurrence.model_source
#print axioms TelescopingRatioRecurrence.model_classification
#print axioms TelescopingRatioRecurrence.positive_index_formula
#print axioms TelescopingRatioRecurrence.source_exists
#print axioms TelescopingRatioRecurrence.source_iff_formula
#print axioms TelescopingRatioRecurrence.source_answer
#print axioms TelescopingRatioRecurrence.term_positive
#print axioms TelescopingRatioRecurrence.term_strict_decrease
#print axioms TelescopingRatioRecurrence.term_reciprocal_bound
#print axioms TelescopingRatioRecurrence.term_tendsto_zero
#print axioms TelescopingRatioRecurrence.source_positive_decay
#print axioms solution
