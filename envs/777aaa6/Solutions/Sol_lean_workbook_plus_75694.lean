-- Prove2me | solution 1 for lean_workbook_plus_75694
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:05:55.42983+00:00
-- url     : https://prove2.me/submissions/2eec8c07-87d7-417c-a6c7-3709c8d4cf77

import Mathlib

set_option autoImplicit false

namespace RationalEuclideanHeight

def Equation (f : ℚ → ℝ) : Prop :=
  f 1 = 1 ∧
    (∀ q : ℚ, 0 < q → f q = f (1 / q)) ∧
    (∀ q : ℚ, 1 < q → (q : ℝ) * f q = ((q : ℝ) + 1) * f (q - 1))

noncomputable def model (q : ℚ) : ℝ := ((q.num : ℝ) + (q.den : ℝ)) / 2

theorem sub_one_num (q : ℚ) : (q - 1).num = q.num - q.den := by
  apply mul_right_cancel₀ (show (q.den : ℤ) ≠ 0 by exact_mod_cast q.den_ne_zero)
  simpa using Rat.substr_num_den' q 1

theorem model_step (q : ℚ) :
    (q : ℝ) * model q = ((q : ℝ) + 1) * model (q - 1) := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  simp only [model, sub_one_num, Rat.sub_ofNat_den]
  push_cast
  rw [Rat.cast_def]
  field_simp
  ring

theorem model_reciprocal (q : ℚ) (hq : 0 < q) : model q = model (1 / q) := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have ha : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hn.le)
  simp only [model, one_div, Rat.num_inv, Rat.den_inv_of_ne_zero hq.ne',
    Int.sign_eq_one_of_pos hn, one_mul]
  push_cast
  rw [ha]
  ring

theorem model_equation : Equation model := by
  refine ⟨?_, model_reciprocal, fun q _ => model_step q⟩
  norm_num [model]
  rfl

theorem step_agreement {f g : ℚ → ℝ} (hf : Equation f) (hg : Equation g)
    (q : ℚ) (hq : 1 < q) (he : f (q - 1) = g (q - 1)) : f q = g q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by linarith)
  apply mul_left_cancel₀ hq0
  rw [hf.2.2 q hq, hg.2.2 q hq, he]

theorem nat_fraction_sub_one (m n : ℕ) (hn : 0 < n) (hmn : n ≤ m) :
    (m : ℚ) / n - 1 = ((m - n : ℕ) : ℚ) / n := by
  rw [Nat.cast_sub hmn]
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  field_simp

theorem nat_fraction_reciprocal (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    1 / ((m : ℚ) / n) = (n : ℚ) / m := by
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  field_simp

theorem unique_on_nat_fractions {f g : ℚ → ℝ} (hf : Equation f) (hg : Equation g)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : f ((m : ℚ) / n) = g ((m : ℚ) / n) := by
  have main : ∀ s : ℕ, ∀ a b : ℕ, 0 < a → 0 < b → a + b = s →
      f ((a : ℚ) / b) = g ((a : ℚ) / b) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a b ha hb hs
      rcases lt_trichotomy a b with hab | hab | hab
      · have hq : 0 < (a : ℚ) / b := by positivity
        rw [hf.2.1 _ hq, hg.2.1 _ hq, nat_fraction_reciprocal a b ha hb]
        have hr : (1 : ℚ) < (b : ℚ) / a := by
          apply (lt_div_iff₀ (by positivity : (0 : ℚ) < a)).2
          norm_num
          exact_mod_cast hab
        apply step_agreement hf hg _ hr
        rw [nat_fraction_sub_one b a ha hab.le]
        exact ih ((b - a) + a) (by omega) (b - a) a (by omega) ha rfl
      · subst b
        have ha0 : (a : ℚ) ≠ 0 := by positivity
        simp only [div_self ha0, hf.1, hg.1]
      · have hq : (1 : ℚ) < (a : ℚ) / b := by
          apply (lt_div_iff₀ (by positivity : (0 : ℚ) < b)).2
          norm_num
          exact_mod_cast hab
        apply step_agreement hf hg _ hq
        rw [nat_fraction_sub_one a b hb hab.le]
        exact ih ((a - b) + b) (by omega) (a - b) b (by omega) hb rfl
  exact main (m + n) m n hm hn rfl

theorem unique_on_positive {f g : ℚ → ℝ} (hf : Equation f) (hg : Equation g)
    (q : ℚ) (hq : 0 < q) : f q = g q := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have hm : 0 < q.num.toNat := by omega
  have he : ((q.num.toNat : ℕ) : ℚ) / q.den = q := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn.le, Rat.num_div_den]
  simpa only [he] using unique_on_nat_fractions hf hg q.num.toNat q.den hm q.pos

theorem classification (f : ℚ → ℝ) :
    Equation f ↔ ∀ q : ℚ, 0 < q → f q = model q := by
  constructor
  · intro hf q hq
    exact unique_on_positive hf model_equation q hq
  · intro hf
    refine ⟨?_, ?_, ?_⟩
    · rw [hf 1 (by norm_num)]
      exact model_equation.1
    · intro q hq
      rw [hf q hq, hf (1 / q) (by positivity)]
      exact model_reciprocal q hq
    · intro q hq
      rw [hf q (by linarith), hf (q - 1) (by linarith)]
      exact model_step q

noncomputable def extension (outside : ℚ → ℝ) (q : ℚ) : ℝ :=
  if 0 < q then model q else outside q

theorem extension_equation (outside : ℚ → ℝ) : Equation (extension outside) := by
  apply (classification _).2
  intro q hq
  simp only [extension, if_pos hq]

theorem extension_nonpositive (outside : ℚ → ℝ) (q : ℚ) (hq : q ≤ 0) :
    extension outside q = outside q := by
  simp only [extension, if_neg (not_lt.mpr hq)]

theorem extension_classification (f : ℚ → ℝ) :
    Equation f ↔ ∃ outside : ℚ → ℝ, f = extension outside := by
  constructor
  · intro hf
    refine ⟨f, ?_⟩
    funext q
    by_cases hq : 0 < q
    · simpa only [extension, if_pos hq] using (classification f).1 hf q hq
    · simp only [extension, if_neg hq]
  · rintro ⟨outside, rfl⟩
    exact extension_equation outside

theorem reduced_fraction_formula (p d : ℕ) (hd : 0 < d) (hpd : p.Coprime d) :
    model ((p : ℚ) / d) = ((p : ℝ) + (d : ℝ)) / 2 := by
  have hc : Nat.Coprime (p : ℤ).natAbs (d : ℤ).natAbs := by simpa using hpd
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hp := Rat.num_div_eq_of_coprime hd' hc
  have hb := Rat.den_div_eq_of_coprime hd' hc
  simp only [Int.cast_natCast] at hp hb
  unfold model
  rw [hp]
  have hdR : (((p : ℚ) / d).den : ℝ) = (d : ℝ) := by exact_mod_cast hb
  push_cast
  rw [hdR]

theorem source_formula {f : ℚ → ℝ} (hf : Equation f) (p d : ℕ)
    (hp : 0 < p) (hd : 0 < d) (hpd : p.Coprime d) :
    f ((p : ℚ) / d) = ((p : ℝ) + (d : ℝ)) / 2 := by
  rw [(classification f).1 hf _ (by positivity), reduced_fraction_formula p d hd hpd]

theorem source_exists : ∃ f : ℚ → ℝ, Equation f := ⟨model, model_equation⟩

theorem posted_impossible (f : ℚ → ℝ) (hf : f 1 = 1)
    (hi : ∀ x : ℚ, f x = f (1 / x))
    (hs : ∀ x : ℚ, (x : ℝ) * f x = ((x : ℝ) + 1) * f (x - 1)) : False := by
  have h2 := hs 2
  have h3 := hs 3
  have hi2 := hi 2
  have hi3 := hi 3
  have hh := hs (1 / 2)
  have ht := hs (1 / 3)
  have hin := hi (-2 / 3)
  have hnh := hs (-1 / 2)
  norm_num at h2 h3 hi2 hi3 hh ht hin hnh
  linarith

end RationalEuclideanHeight

theorem solution (f : ℚ → ℝ) (hf : f 1 = 1) (hf1 : ∀ x, f x = f (1 / x))
    (hf2 : ∀ x, x * f x = (x + 1) * f (x - 1)) : ∀ x, f x = 1 := by
  exact (RationalEuclideanHeight.posted_impossible f hf hf1 hf2).elim
