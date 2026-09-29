-- Prove2me | solution 1 for poly_alt_sign_compare
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T12:51:31.322286+00:00
-- url     : https://prove2.me/submissions/2714804f-9674-4bb1-96c1-d6c9c93d2060

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Polynomial Set

namespace PolyAltSign

/-- IVT: if a polynomial changes sign on `[a,b]`, it has a root in `(a,b)`. -/
lemma exists_root_of_sign_change (R : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : R.eval a * R.eval b < 0) : ∃ r ∈ Set.Ioo a b, R.IsRoot r := by
  have hcont : ContinuousOn (fun x => R.eval x) (Set.Icc a b) := (Polynomial.continuous R).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- R(a) > 0 > R(b): use intermediate_value_Ioo'.
    have h0 : (0 : ℝ) ∈ Set.Ioo (R.eval b) (R.eval a) := ⟨hb, ha⟩
    have := intermediate_value_Ioo' hab.le hcont h0
    obtain ⟨r, hr1, hr2⟩ := this
    exact ⟨r, hr1, hr2⟩
  · -- R(a) < 0 < R(b): use intermediate_value_Ioo.
    have h0 : (0 : ℝ) ∈ Set.Ioo (R.eval a) (R.eval b) := ⟨ha, hb⟩
    have := intermediate_value_Ioo hab.le hcont h0
    obtain ⟨r, hr1, hr2⟩ := this
    exact ⟨r, hr1, hr2⟩

/-- The core root-counting: an alternating polynomial with extra outer root. -/
lemma no_outer_root (R : Polynomial ℝ) (n : ℕ) (t : ℕ → ℝ)
    (ht : ∀ i j : ℕ, i < j → j ≤ n → t j < t i)
    (hdeg : R.natDegree ≤ n)
    (halt : ∀ i : ℕ, i ≤ n → 0 < (-1:ℝ)^i * R.eval (t i))
    (c : ℝ) (hc : t 0 ≤ c ∨ c ≤ t n) (hroot : R.IsRoot c) : False := by
  -- R ≠ 0 since R(t 0) > 0.
  have hR0 : R ≠ 0 := by
    intro hR
    have := halt 0 (Nat.zero_le n)
    simp [hR] at this
  -- For each i < n, R changes sign on (t(i+1), t i), giving a root r_i.
  have hroots : ∀ i : ℕ, i < n → ∃ r ∈ Set.Ioo (t (i + 1)) (t i), R.IsRoot r := by
    intro i hi
    apply exists_root_of_sign_change R (ht i (i+1) (Nat.lt_succ_self i) hi)
    -- R(t(i+1)) · R(t i) < 0.
    have h1 := halt (i + 1) hi
    have h2 := halt i (Nat.le_of_lt hi)
    have heq : (-1:ℝ)^(i+1) = -(-1:ℝ)^i := by rw [pow_succ]; ring
    rw [heq] at h1
    nlinarith [sq_nonneg ((-1:ℝ)^i)]
  -- Choice function for the roots.
  classical
  let r : ℕ → ℝ := fun i => if hi : i < n then (hroots i hi).choose else c
  have hr_mem : ∀ i, i < n → r i ∈ Set.Ioo (t (i + 1)) (t i) := by
    intro i hi
    simp only [r, dif_pos hi]
    exact (hroots i hi).choose_spec.1
  have hr_root : ∀ i, i < n → R.IsRoot (r i) := by
    intro i hi
    simp only [r, dif_pos hi]
    exact (hroots i hi).choose_spec.2
  -- r i ∈ (t n, t 0) for all i < n.
  have hr_inner : ∀ i, i < n → t n < r i ∧ r i < t 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hr_mem i hi
    constructor
    · rcases Nat.lt_or_ge (i + 1) n with h | h
      · exact lt_trans (ht (i+1) n h le_rfl) h1
      · have : i + 1 = n := le_antisymm hi h
        rw [this] at h1; exact h1
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact h2
      · exact lt_trans h2 (ht 0 i h (Nat.le_of_lt hi))
  -- The r i are pairwise distinct.
  have hr_inj : ∀ i j, i < n → j < n → i < j → r i ≠ r j := by
    intro i j hi hj hij
    obtain ⟨hi1, hi2⟩ := hr_mem i hi
    obtain ⟨hj1, hj2⟩ := hr_mem j hj
    have htij : t j ≤ t (i + 1) := by
      rcases Nat.lt_or_ge (i + 1) j with h | h
      · exact (ht (i+1) j h (Nat.le_of_lt hj)).le
      · have : i + 1 = j := le_antisymm hij h
        rw [this]
    intro heq
    linarith [heq ▸ hi1]
  -- c ≠ r i for all i < n (c is outside (t n, t 0)).
  have hc_ne : ∀ i, i < n → c ≠ r i := by
    intro i hi heq
    obtain ⟨hri1, hri2⟩ := hr_inner i hi
    rcases hc with hc1 | hc2
    · linarith [heq ▸ hc1]
    · linarith [heq ▸ hc2]
  -- Build the finset S.
  let S : Finset ℝ := (Finset.range n).image r ∪ {c}
  have hS_sub : S ⊆ R.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hR0]
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton] at hx
    rcases hx with ⟨i, hi, heq⟩ | heq
    · rw [← heq]; exact hr_root i hi
    · rw [heq]; exact hroot
  have hr_injOn : Set.InjOn r ↑(Finset.range n) := by
    intro i hi j hj heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact hr_inj i j hi hj h heq
    · exact hr_inj j i hj hi (lt_of_le_of_ne h (Ne.symm hne)) heq.symm
  have hdisj : Disjoint ((Finset.range n).image r) {c} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨i, hi, heq⟩
    exact hc_ne i (Finset.mem_range.mp hi) heq.symm
  have hS_card : S.card = n + 1 := by
    show ((Finset.range n).image r ∪ {c}).card = n + 1
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
        Finset.card_image_of_injOn hr_injOn, Finset.card_range]
  have := calc n + 1 = S.card := hS_card.symm
    _ ≤ R.roots.toFinset.card := Finset.card_le_card hS_sub
    _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := Polynomial.card_roots' R
    _ ≤ n := hdeg
  omega

end PolyAltSign

open PolyAltSign

theorem solution : poly_alt_sign_compare := by
  intro Tp p n t ht hTdeg hpdeg halt hcmp c hc
  by_contra hcontra
  push_neg at hcontra
  -- Case 1: Tp(c) = 0. Then Tp has an outer root, contradiction.
  rcases eq_or_ne (Tp.eval c) 0 with hTc | hTc
  · exact no_outer_root Tp n t ht hTdeg halt c hc hTc
  -- Case 2: Tp(c) ≠ 0. Let μ := Tp(c)/p(c).
  have hpc : p.eval c ≠ 0 := by
    intro hpc
    rw [hpc, abs_zero] at hcontra
    exact absurd hcontra (not_lt.mpr (abs_nonneg _))
  have hmu : |Tp.eval c / p.eval c| < 1 := by
    rw [abs_div, div_lt_one (abs_pos.mpr hpc)]
    exact hcontra
  set μ := Tp.eval c / p.eval c with hμ_def
  set R := Tp - C μ * p with hR_def
  have hR_eval : ∀ x : ℝ, R.eval x = Tp.eval x - μ * p.eval x := by
    intro x; rw [hR_def]; simp [Polynomial.eval_sub, Polynomial.eval_mul]
  -- R(c) = 0.
  have hRc : R.IsRoot c := by
    rw [Polynomial.IsRoot, hR_eval, hμ_def]
    field_simp
    ring
  -- deg R ≤ n.
  have hRdeg : R.natDegree ≤ n := by
    rw [hR_def]
    calc (Tp - C μ * p).natDegree ≤ max Tp.natDegree (C μ * p).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ max Tp.natDegree p.natDegree := by
          apply max_le_max le_rfl
          exact Polynomial.natDegree_C_mul_le _ _
      _ ≤ n := max_le hTdeg hpdeg
  -- R alternates at t i.
  have hRalt : ∀ i : ℕ, i ≤ n → 0 < (-1:ℝ)^i * R.eval (t i) := by
    intro i hi
    rw [hR_eval]
    have h1 := halt i hi
    have h2 := hcmp i hi
    have h3 : |μ * p.eval (t i)| ≤ |μ| * |Tp.eval (t i)| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg μ)
    have hTi_ne : Tp.eval (t i) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact absurd h1 (lt_irrefl 0)
    have hTi_pos : 0 < |Tp.eval (t i)| := abs_pos.mpr hTi_ne
    -- (-1)^i Tp(t i) = |Tp(t i)|
    have hsign : (-1:ℝ)^i * Tp.eval (t i) = |Tp.eval (t i)| := by
      have hab : |(-1:ℝ)^i * Tp.eval (t i)| = |Tp.eval (t i)| := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [← hab, abs_of_pos h1]
    calc (0:ℝ) < (1 - |μ|) * |Tp.eval (t i)| := by
          apply mul_pos _ hTi_pos; linarith [hmu]
      _ = |Tp.eval (t i)| - |μ| * |Tp.eval (t i)| := by ring
      _ ≤ (-1:ℝ)^i * Tp.eval (t i) - |μ * p.eval (t i)| := by
          rw [hsign]; linarith [h3]
      _ ≤ (-1:ℝ)^i * Tp.eval (t i) - (-1:ℝ)^i * (μ * p.eval (t i)) := by
          have := neg_abs_le ((-1:ℝ)^i * (μ * p.eval (t i)))
          have habs : |(-1:ℝ)^i * (μ * p.eval (t i))| = |μ * p.eval (t i)| := by
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          linarith [le_abs_self ((-1:ℝ)^i * (μ * p.eval (t i))), habs]
      _ = (-1:ℝ)^i * (Tp.eval (t i) - μ * p.eval (t i)) := by ring
  -- Apply no_outer_root.
  exact no_outer_root R n t ht hRdeg hRalt c hc hRc
