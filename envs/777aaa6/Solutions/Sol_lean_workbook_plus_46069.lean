-- Prove2me | solution 1 for lean_workbook_plus_46069
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:29:14.777587+00:00
-- url     : https://prove2.me/submissions/ea07b16f-f98c-490b-85fe-7fca1fb0690f

import Mathlib

namespace FiniteRealSigning

theorem balancing_step {r t M : ℝ} (hr : |r| ≤ M) (ht : |t| ≤ M) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ |r + e * t| ≤ M ∧
      (r + e * t) ^ 2 ≤ r ^ 2 + t ^ 2 := by
  obtain ⟨hrl, hru⟩ := abs_le.mp hr
  obtain ⟨htl, htu⟩ := abs_le.mp ht
  rcases le_total r 0 with hr0 | hr0 <;> rcases le_total t 0 with ht0 | ht0
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · apply abs_le.mpr; constructor <;> linarith
    · nlinarith only [mul_nonneg_of_nonpos_of_nonpos hr0 ht0]
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · apply abs_le.mpr; constructor <;> linarith
    · nlinarith only [mul_nonpos_of_nonpos_of_nonneg hr0 ht0]
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · apply abs_le.mpr; constructor <;> linarith
    · nlinarith only [mul_nonpos_of_nonneg_of_nonpos hr0 ht0]
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · apply abs_le.mpr; constructor <;> linarith
    · nlinarith only [mul_nonneg hr0 ht0]

theorem finite_balance {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ i ∈ s, |x i| ≤ M) :
    ∃ e : ι → ℝ, (∀ i, e i = 1 ∨ e i = -1) ∧
      |∑ i ∈ s, e i * x i| ≤ M ∧
      (∑ i ∈ s, e i * x i) ^ 2 ≤ ∑ i ∈ s, (x i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simpa using hM, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨e, he, hb, hq⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    obtain ⟨d, hd, hdb, hdq⟩ := balancing_step hb (hx a (Finset.mem_insert_self a s))
    let e' := Function.update e a d
    have hes : ∑ i ∈ s, e' i * x i = ∑ i ∈ s, e i * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := by intro h; subst i; exact ha hi
      simp [e', Function.update_of_ne hia]
    have hei : ∑ i ∈ insert a s, e' i * x i = (∑ i ∈ s, e i * x i) + d * x a := by
      rw [Finset.sum_insert ha, hes]
      simp [e', add_comm]
    refine ⟨e', ?_, ?_, ?_⟩
    · intro i
      by_cases hia : i = a
      · subst i; simpa [e'] using hd
      · simpa [e', Function.update_of_ne hia] using he i
    · rwa [hei]
    · rw [hei, Finset.sum_insert ha]
      linarith only [hdq, hq]

theorem bounded_signing (n : ℕ) (x : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ i, |x i| ≤ M) :
    ∃ e : Fin n → ℝ, (∀ i, e i = 1 ∨ e i = -1) ∧
      |∑ i, e i * x i| ≤ M ∧ (∑ i, e i * x i) ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  exact finite_balance Finset.univ x hM (fun i _ => hx i)

theorem source (n : ℕ) (x : Fin n → ℝ) :
    ∃ e : Fin n → ℝ, (∀ i, e i = 1 ∨ e i = -1) ∧
      (∑ i, e i * x i) ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  have hM : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  have hx : ∀ i, |x i| ≤ ∑ j, |x j| := by
    intro i
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  obtain ⟨e, he, _, hq⟩ := bounded_signing n x hM hx
  exact ⟨e, he, hq⟩

theorem sharp_energy_constant (k : ℝ) :
    (∀ (n : ℕ) (x : Fin n → ℝ), ∃ e : Fin n → ℝ,
      (∀ i, e i = 1 ∨ e i = -1) ∧
      (∑ i, e i * x i) ^ 2 ≤ k * ∑ i, (x i) ^ 2) ↔ 1 ≤ k := by
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := h 1 (fun _ => 1)
    rcases he 0 with hs | hs <;> simpa [Fin.sum_univ_one, hs] using hb
  · intro hk n x
    obtain ⟨e, he, hb⟩ := source n x
    refine ⟨e, he, hb.trans ?_⟩
    exact le_mul_of_one_le_left (Finset.sum_nonneg (fun i _ => sq_nonneg (x i))) hk

theorem sharp_amplitude_constant (k : ℝ) :
    (∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, |x i| ≤ 1) →
      ∃ e : Fin n → ℝ, (∀ i, e i = 1 ∨ e i = -1) ∧ |∑ i, e i * x i| ≤ k) ↔
      1 ≤ k := by
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := h 1 (fun _ => 1) (by simp)
    rcases he 0 with hs | hs <;> simpa [Fin.sum_univ_one, hs] using hb
  · intro hk n x hx
    obtain ⟨e, he, hb, _⟩ := bounded_signing n x (by norm_num) hx
    exact ⟨e, he, hb.trans hk⟩

end FiniteRealSigning

theorem solution (n : ℕ) (x : Fin n → ℝ) :
    ∃ ε : Fin n → ℝ, ∀ i, ε i = 1 ∨ ε i = -1 ∧
      (∑ i, ε i * x i) ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  obtain ⟨e, he, hb⟩ := FiniteRealSigning.source n x
  refine ⟨e, fun i => ?_⟩
  rcases he i with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hb⟩

#print axioms FiniteRealSigning.balancing_step
#print axioms FiniteRealSigning.finite_balance
#print axioms FiniteRealSigning.bounded_signing
#print axioms FiniteRealSigning.source
#print axioms FiniteRealSigning.sharp_energy_constant
#print axioms FiniteRealSigning.sharp_amplitude_constant
#print axioms solution
