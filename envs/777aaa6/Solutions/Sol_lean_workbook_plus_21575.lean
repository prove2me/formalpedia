-- Prove2me | solution 1 for lean_workbook_plus_21575
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:28:10.121531+00:00
-- url     : https://prove2.me/submissions/f8a7919a-cfb2-4452-925b-4eeeceb1dd33

import Mathlib

noncomputable section

namespace DistinctReciprocalProductMaximum

def P (α β γ : ℝ) (a b c : ℕ) : ℝ :=
  (α + 1 / (a : ℝ)) * (β + 1 / (b : ℝ)) * (γ + 1 / (c : ℝ))

theorem factor_pos {α : ℝ} {a : ℕ} (hα : 0 ≤ α) (ha : 0 < a) :
    0 < α + 1 / (a : ℝ) := by positivity

theorem reciprocal_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    1 / (b : ℝ) ≤ 1 / (a : ℝ) := by
  apply one_div_le_one_div_of_le <;> exact_mod_cast ‹_›

theorem reciprocal_lt {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    1 / (b : ℝ) < 1 / (a : ℝ) := by
  apply one_div_lt_one_div_of_lt <;> exact_mod_cast ‹_›

theorem swap_first {α β γ : ℝ} {a b c : ℕ}
    (hab : α ≤ β) (hγ : 0 ≤ γ) (hb : 0 < b) (hc : 0 < c) (hba : b ≤ a) :
    P α β γ a b c ≤ P α β γ b a c := by
  have hr := reciprocal_le hb hba
  have hf := factor_pos hγ hc
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hr)) hf.le
  unfold P
  nlinarith

theorem swap_last {α β γ : ℝ} {a b c : ℕ}
    (hα : 0 ≤ α) (hbc : β ≤ γ) (ha : 0 < a) (hc : 0 < c) (hcb : c ≤ b) :
    P α β γ a b c ≤ P α β γ a c b := by
  have hr := reciprocal_le hc hcb
  have hf := factor_pos hα ha
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hr)) hf.le
  unfold P
  nlinarith

theorem swap_first_strict {α β γ : ℝ} {a b c : ℕ}
    (hab : α < β) (hγ : 0 ≤ γ) (hb : 0 < b) (hc : 0 < c) (hba : b < a) :
    P α β γ a b c < P α β γ b a c := by
  have hr := reciprocal_lt hb hba
  have hf := factor_pos hγ hc
  have h := mul_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hr)) hf
  unfold P
  nlinarith

theorem swap_last_strict {α β γ : ℝ} {a b c : ℕ}
    (hα : 0 ≤ α) (hbc : β < γ) (ha : 0 < a) (hc : 0 < c) (hcb : c < b) :
    P α β γ a b c < P α β γ a c b := by
  have hr := reciprocal_lt hc hcb
  have hf := factor_pos hα ha
  have h := mul_pos (mul_pos (sub_pos.mpr hbc) (sub_pos.mpr hr)) hf
  unfold P
  nlinarith

theorem coordinate_bound {α β γ : ℝ} {a b c x y z : ℕ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxa : x ≤ a) (hyb : y ≤ b) (hzc : z ≤ c) :
    P α β γ a b c ≤ P α β γ x y z := by
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hb : 0 < b := lt_of_lt_of_le hy hyb
  have hc : 0 < c := lt_of_lt_of_le hz hzc
  have h1 := reciprocal_le hx hxa
  have h2 := reciprocal_le hy hyb
  have h3 := reciprocal_le hz hzc
  unfold P
  exact mul_le_mul (mul_le_mul (by linarith) (by linarith)
    (factor_pos hβ hb).le (factor_pos hα hx).le) (by linarith)
    (factor_pos hγ hc).le (mul_nonneg (factor_pos hα hx).le (factor_pos hβ hy).le)

theorem coordinate_equality {α β γ : ℝ} {a b c x y z : ℕ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxa : x ≤ a) (hyb : y ≤ b) (hzc : z ≤ c) :
    P α β γ a b c = P α β γ x y z ↔ a = x ∧ b = y ∧ c = z := by
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hb : 0 < b := lt_of_lt_of_le hy hyb
  have hc : 0 < c := lt_of_lt_of_le hz hzc
  have h1 : α + 1 / (a : ℝ) ≤ α + 1 / (x : ℝ) := by
    linarith [reciprocal_le hx hxa]
  have h2 : β + 1 / (b : ℝ) ≤ β + 1 / (y : ℝ) := by
    linarith [reciprocal_le hy hyb]
  have h3 : γ + 1 / (c : ℝ) ≤ γ + 1 / (z : ℝ) := by
    linarith [reciprocal_le hz hzc]
  have h12 := mul_le_mul h1 h2 (factor_pos hβ hb).le (factor_pos hα hx).le
  unfold P
  rw [mul_eq_mul_iff_eq_and_eq_of_pos h12 h3
    (mul_pos (factor_pos hα ha) (factor_pos hβ hb)) (factor_pos hγ hz)]
  rw [mul_eq_mul_iff_eq_and_eq_of_pos h1 h2 (factor_pos hα ha) (factor_pos hβ hy)]
  simp only [add_right_inj, one_div, inv_inj, Nat.cast_inj]
  tauto

theorem ordered_bound {α β γ : ℝ} {m a b c : ℕ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hm : 0 < m)
    (hma : m ≤ a) (hab : a < b) (hbc : b < c) :
    P α β γ a b c ≤ P α β γ m (m + 1) (m + 2) := by
  exact coordinate_bound hα hβ hγ hm (by omega) (by omega) hma (by omega) (by omega)

theorem maximum {α β γ : ℝ} {m a b c : ℕ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβγ : β ≤ γ) (hm : 0 < m)
    (hma : m ≤ a) (hmb : m ≤ b) (hmc : m ≤ c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    P α β γ a b c ≤ P α β γ m (m + 1) (m + 2) := by
  have hβ := hα.trans hαβ
  have hγ := hβ.trans hβγ
  have ha := hm.trans_le hma
  have hb := hm.trans_le hmb
  have hc := hm.trans_le hmc
  by_cases hab' : a < b
  · by_cases hbc' : b < c
    · exact ordered_bound hα hβ hγ hm hma hab' hbc'
    · have hcb : c < b := by omega
      by_cases hac : a < c
      · exact (swap_last hα hβγ ha hc hcb.le).trans
          (ordered_bound hα hβ hγ hm hma hac hcb)
      · have hca' : c < a := by omega
        exact (swap_last hα hβγ ha hc hcb.le).trans
          ((swap_first hαβ hγ hc hb hca'.le).trans
            (ordered_bound hα hβ hγ hm hmc hca' hab'))
  · have hba : b < a := by omega
    by_cases hac : a < c
    · exact (swap_first hαβ hγ hb hc hba.le).trans
        (ordered_bound hα hβ hγ hm hmb hba hac)
    · have hca' : c < a := by omega
      by_cases hbc' : b < c
      · exact (swap_first hαβ hγ hb hc hba.le).trans
          ((swap_last hα hβγ hb hc hca'.le).trans
            (ordered_bound hα hβ hγ hm hmb hbc' hca'))
      · have hcb : c < b := by omega
        exact (swap_first hαβ hγ hb hc hba.le).trans
          ((swap_last hα hβγ hb hc hca'.le).trans
            ((swap_first hαβ hγ hc ha hcb.le).trans
              (ordered_bound hα hβ hγ hm hmc hcb hba)))

theorem maximum_equality {α β γ : ℝ} {m a b c : ℕ}
    (hα : 0 ≤ α) (hαβ : α < β) (hβγ : β < γ) (hm : 0 < m)
    (hma : m ≤ a) (hmb : m ≤ b) (hmc : m ≤ c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    P α β γ a b c = P α β γ m (m + 1) (m + 2) ↔
      a = m ∧ b = m + 1 ∧ c = m + 2 := by
  constructor
  · intro he
    have hβ := hα.trans hαβ.le
    have hγ := hβ.trans hβγ.le
    have ha := hm.trans_le hma
    have hb := hm.trans_le hmb
    have hc := hm.trans_le hmc
    have hab' : a < b := by
      by_contra hn
      have hba : b < a := by omega
      have hs := swap_first_strict hαβ hγ hb hc hba
      have hu := maximum hα hαβ.le hβγ.le hm hmb hma hmc hab.symm hca.symm hbc.symm
      linarith
    have hbc' : b < c := by
      by_contra hn
      have hcb : c < b := by omega
      have hs := swap_last_strict hα hβγ ha hc hcb
      have hu := maximum hα hαβ.le hβγ.le hm hma hmc hmb hca.symm hbc.symm hab.symm
      linarith
    exact (coordinate_equality hα hβ hγ hm (by omega) (by omega) hma
      (by omega) (by omega)).mp he
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem source {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (1 + 1 / (a : ℝ)) * (2 + 1 / (b : ℝ)) * (3 + 1 / (c : ℝ)) ≤ 91 / 8 := by
  have h := maximum (α := 1) (β := 2) (γ := 3) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by omega)
    (by omega) (by omega) (by omega) hab hbc hca
  norm_num [P] at h ⊢
  exact h

theorem source_equality {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (1 + 1 / (a : ℝ)) * (2 + 1 / (b : ℝ)) * (3 + 1 / (c : ℝ)) = 91 / 8 ↔
      a = 2 ∧ b = 3 ∧ c = 4 := by
  have h := maximum_equality (α := 1) (β := 2) (γ := 3) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by omega)
    (by omega) (by omega) (by omega) hab hbc hca
  norm_num [P] at h ⊢
  exact h

theorem best_bound (K : ℝ) :
    (∀ a b c : ℕ, a ≠ b → b ≠ c → c ≠ a → 1 < a → 1 < b → 1 < c →
      (1 + 1 / (a : ℝ)) * (2 + 1 / (b : ℝ)) * (3 + 1 / (c : ℝ)) ≤ K) ↔
      91 / 8 ≤ K := by
  constructor
  · intro h
    have ht := h 2 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at ht
    exact ht
  · intro h a b c hab hbc hca ha hb hc
    exact (source hab hbc hca ha hb hc).trans h

end DistinctReciprocalProductMaximum

theorem solution (a b c : ℕ) (_hab : a ≠ b) (_hbc : b ≠ c) (_hca : c ≠ a)
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (1 + 1 / a) * (2 + 1 / b) * (3 + 1 / c) ≤ 91 / 8 := by
  rw [Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hc]
  norm_num

#print axioms DistinctReciprocalProductMaximum.P
#print axioms DistinctReciprocalProductMaximum.factor_pos
#print axioms DistinctReciprocalProductMaximum.reciprocal_le
#print axioms DistinctReciprocalProductMaximum.reciprocal_lt
#print axioms DistinctReciprocalProductMaximum.swap_first
#print axioms DistinctReciprocalProductMaximum.swap_last
#print axioms DistinctReciprocalProductMaximum.swap_first_strict
#print axioms DistinctReciprocalProductMaximum.swap_last_strict
#print axioms DistinctReciprocalProductMaximum.coordinate_bound
#print axioms DistinctReciprocalProductMaximum.coordinate_equality
#print axioms DistinctReciprocalProductMaximum.ordered_bound
#print axioms DistinctReciprocalProductMaximum.maximum
#print axioms DistinctReciprocalProductMaximum.maximum_equality
#print axioms DistinctReciprocalProductMaximum.source
#print axioms DistinctReciprocalProductMaximum.source_equality
#print axioms DistinctReciprocalProductMaximum.best_bound
#print axioms solution
