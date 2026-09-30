-- Prove2me | solution 1 for lean_workbook_plus_4843
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T00:55:09.347318+00:00
-- url     : https://prove2.me/submissions/882183cf-b40e-4eec-95b4-dcce7b59949b

import Mathlib

set_option autoImplicit false

namespace SignedBinaryQuinticSharpBound

def value (a b : ℝ) : ℝ := (a - b) * a ^ 2 * b ^ 2

noncomputable def radius (a b : ℝ) : ℝ := Real.sqrt ((a ^ 2 + b ^ 2) / 5)

noncomputable def signedConstant : ℝ := 25 * Real.sqrt 10 / 4

theorem radius_identity (a b : ℝ) :
    0 ≤ radius a b ∧ a ^ 2 + b ^ 2 = 5 * radius a b ^ 2 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 5)
  change a ^ 2 + b ^ 2 = 5 * (Real.sqrt ((a ^ 2 + b ^ 2) / 5)) ^ 2
  linarith

theorem real_normalized (a b r : ℝ) (hr : 0 ≤ r)
    (hn : a ^ 2 + b ^ 2 = 5 * r ^ 2) :
    value a b ≤ signedConstant * r ^ 5 ∧
      (value a b = signedConstant * r ^ 5 ↔ b = -a ∧ 0 ≤ a) := by
  by_cases hr0 : r = 0
  · have ha0 : a = 0 := by nlinarith [sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a]
    simp [ha0, hb0, hr0, value]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let s : ℝ := Real.sqrt 10
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs2 : s ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hv : value a b = (a - b) * (a * b) ^ 2 := by unfold value; ring
  have hu : a - b ≤ s * r := by
    apply le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, hs2]
    nlinarith only [hn, sq_nonneg (a + b)]
  have hab : (a * b) ^ 2 ≤ 25 * r ^ 4 / 4 := by
    have hh : 4 * (a * b) ^ 2 ≤ (a ^ 2 + b ^ 2) ^ 2 := by
      nlinarith only [sq_nonneg (a ^ 2 - b ^ 2)]
    rw [hn] at hh
    nlinarith only [hh]
  have hfirst := mul_le_mul_of_nonneg_right hu (sq_nonneg (a * b))
  have hsecond := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ s * r)
  have hlast : s * r * (25 * r ^ 4 / 4) = signedConstant * r ^ 5 := by
    dsimp [signedConstant, s]
    ring
  have hbound : value a b ≤ signedConstant * r ^ 5 := by
    rw [hv]
    linarith only [hfirst, hsecond, hlast]
  refine ⟨hbound, ?_⟩
  constructor
  · intro he
    have hpos : 0 < signedConstant * r ^ 5 := by
      unfold signedConstant
      positivity
    have habp : 0 < (a * b) ^ 2 := by
      by_contra hbad
      have hz : (a * b) ^ 2 = 0 := le_antisymm (le_of_not_gt hbad) (sq_nonneg _)
      rw [hv, hz, mul_zero] at he
      linarith
    have hue : a - b = s * r := by
      apply mul_right_cancel₀ (ne_of_gt habp)
      rw [hv] at he
      linarith only [he, hfirst, hsecond, hlast]
    have hsq : (a - b) ^ 2 = 10 * r ^ 2 := by rw [hue, mul_pow, hs2]
    have hsum : a + b = 0 := by
      have hz : (a + b) ^ 2 = 0 := by nlinarith only [hn, hsq]
      exact sq_eq_zero_iff.mp hz
    have hu0 : 0 ≤ a - b := by rw [hue]; positivity
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hb, ha⟩
    have hue : a - b = s * r := by
      apply (sq_eq_sq₀ (by linarith : 0 ≤ a - b) (by positivity : 0 ≤ s * r)).mp
      rw [mul_pow, hs2]
      rw [hb] at hn ⊢
      nlinarith only [hn]
    have habe : (a * b) ^ 2 = 25 * r ^ 4 / 4 := by
      have hh := congrArg (fun x : ℝ => x ^ 2) hn
      rw [hb] at hh ⊢
      nlinarith only [hh]
    rw [hv, hue, habe, hlast]

theorem nonnegative_normalized (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hn : a ^ 2 + b ^ 2 = 5 * r ^ 2) :
    value a b ≤ 4 * r ^ 5 ∧ (value a b = 4 * r ^ 5 ↔ a = 2 * b) := by
  by_cases hr0 : r = 0
  · have ha0 : a = 0 := by nlinarith [sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a]
    simp [ha0, hb0, hr0, value]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hr5 : 0 < 4 * r ^ 5 := by positivity
  by_cases horder : b ≤ a
  · let u := a - b
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hu2 : u ^ 2 ≤ 5 * r ^ 2 := by
      have hp : 0 ≤ a * b := mul_nonneg ha hb
      dsimp [u]
      nlinarith only [hn, hp]
    have hab : 5 * r ^ 2 - u ^ 2 = 2 * a * b := by
      dsimp [u]
      nlinarith only [hn]
    have hv : 4 * value a b = u * (5 * r ^ 2 - u ^ 2) ^ 2 := by
      rw [hab]
      dsimp [value, u]
      ring
    let q := 16 * r ^ 3 + 7 * r ^ 2 * u - 2 * r * u ^ 2 - u ^ 3
    have hq : 0 < q := by
      have h1 := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 2 * r)
      have h2 := mul_le_mul_of_nonneg_left hu2 hu
      have h3 : 0 ≤ r ^ 2 * u := by positivity
      have h4 : 0 < r ^ 3 := pow_pos hrp 3
      dsimp [q]
      nlinarith only [h1, h2, h3, h4]
    have hgap : 4 * (4 * r ^ 5 - value a b) = (r - u) ^ 2 * q := by
      calc
        4 * (4 * r ^ 5 - value a b) = 16 * r ^ 5 - u * (5 * r ^ 2 - u ^ 2) ^ 2 := by
          linarith only [hv]
        _ = (r - u) ^ 2 * q := by dsimp [q]; ring
    have hp : 0 ≤ (r - u) ^ 2 * q := mul_nonneg (sq_nonneg _) hq.le
    refine ⟨by linarith only [hgap, hp], ?_⟩
    constructor
    · intro he
      have hz : (r - u) ^ 2 * q = 0 := by linarith only [hgap, he]
      have hru : r = u := by
        have hz2 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hq)
        have hh := sq_eq_zero_iff.mp hz2
        linarith
      have hf : (2 * a - b) * (a - 2 * b) = 0 := by
        rw [hru] at hn
        dsimp [u] at hn
        nlinarith only [hn]
      rcases mul_eq_zero.mp hf with hleft | hright
      · have ha0 : a = 0 := by linarith
        have hb0 : b = 0 := by linarith
        simp [u, ha0, hb0] at hru
        exact False.elim (hr0 hru)
      · linarith
    · intro he
      have hbr : b = r := by
        apply (sq_eq_sq₀ hb hr).mp
        rw [he] at hn
        nlinarith only [hn]
      have hru : r - u = 0 := by dsimp [u]; linarith
      rw [hru] at hgap
      norm_num at hgap
      linarith
  · have hval : value a b ≤ 0 := by
      unfold value
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)
    refine ⟨by linarith, ?_⟩
    constructor
    · intro he
      linarith
    · intro he
      exfalso
      linarith

theorem real_bound (a b : ℝ) : value a b ≤ signedConstant * radius a b ^ 5 :=
  (real_normalized a b (radius a b) (radius_identity a b).1 (radius_identity a b).2).1

theorem real_equality (a b : ℝ) :
    value a b = signedConstant * radius a b ^ 5 ↔ b = -a ∧ 0 ≤ a :=
  (real_normalized a b (radius a b) (radius_identity a b).1 (radius_identity a b).2).2

theorem nonnegative_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    value a b ≤ 4 * radius a b ^ 5 :=
  (nonnegative_normalized a b (radius a b) ha hb
    (radius_identity a b).1 (radius_identity a b).2).1

theorem nonnegative_equality (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    value a b = 4 * radius a b ^ 5 ↔ a = 2 * b :=
  (nonnegative_normalized a b (radius a b) ha hb
    (radius_identity a b).1 (radius_identity a b).2).2

theorem nonnegative_model : radius 2 1 = 1 ∧ value 2 1 = 4 := by
  norm_num [radius, value]
  rfl

theorem real_model :
    radius (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2) = 1 ∧
      value (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2) = signedConstant := by
  have hs : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 10 / 2) ^ 2 + (-Real.sqrt 10 / 2) ^ 2 = 5 := by nlinarith
  have hr : radius (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2) = 1 := by
    unfold radius
    rw [hn]
    norm_num
  refine ⟨hr, ?_⟩
  have he := (real_equality (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2)).2
    ⟨by ring, by positivity⟩
  simpa [hr] using he

theorem real_coefficient_iff (k : ℝ) :
    (∀ a b : ℝ, value a b ≤ k * radius a b ^ 5) ↔ signedConstant ≤ k := by
  constructor
  · intro h
    simpa only [real_model.1, real_model.2, one_pow, mul_one] using
      h (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2)
  · intro hk a b
    exact (real_bound a b).trans
      (mul_le_mul_of_nonneg_right hk (pow_nonneg (radius_identity a b).1 5))

theorem nonnegative_coefficient_iff (k : ℝ) :
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → value a b ≤ k * radius a b ^ 5) ↔ 4 ≤ k := by
  constructor
  · intro h
    simpa only [nonnegative_model.1, nonnegative_model.2, one_pow, mul_one] using
      h 2 1 (by norm_num) (by norm_num)
  · intro hk a b ha hb
    exact (nonnegative_bound a b ha hb).trans
      (mul_le_mul_of_nonneg_right hk (pow_nonneg (radius_identity a b).1 5))

theorem signed_constant_gt_four : 4 < signedConstant := by
  have h : (3 : ℝ) < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  unfold signedConstant
  linarith

theorem source_counterexample :
    4 * (Real.sqrt (((Real.sqrt 10 / 2) ^ 2 + (-Real.sqrt 10 / 2) ^ 2) / 5)) ^ 5 <
      (Real.sqrt 10 / 2 - -Real.sqrt 10 / 2) *
        (Real.sqrt 10 / 2) ^ 2 * (-Real.sqrt 10 / 2) ^ 2 := by
  change 4 * radius (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2) ^ 5 <
    value (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2)
  rw [real_model.1, real_model.2]
  simpa using signed_constant_gt_four

end SignedBinaryQuinticSharpBound

theorem solution : ¬ (∀ a b : ℝ,
    4 * (Real.sqrt ((a ^ 2 + b ^ 2) / 5)) ^ 5 ≥ (a - b) * a ^ 2 * b ^ 2) := by
  intro h
  exact (not_le_of_gt SignedBinaryQuinticSharpBound.source_counterexample)
    (h (Real.sqrt 10 / 2) (-Real.sqrt 10 / 2))

#print axioms SignedBinaryQuinticSharpBound.value
#print axioms SignedBinaryQuinticSharpBound.radius
#print axioms SignedBinaryQuinticSharpBound.signedConstant
#print axioms SignedBinaryQuinticSharpBound.radius_identity
#print axioms SignedBinaryQuinticSharpBound.real_normalized
#print axioms SignedBinaryQuinticSharpBound.nonnegative_normalized
#print axioms SignedBinaryQuinticSharpBound.real_bound
#print axioms SignedBinaryQuinticSharpBound.real_equality
#print axioms SignedBinaryQuinticSharpBound.nonnegative_bound
#print axioms SignedBinaryQuinticSharpBound.nonnegative_equality
#print axioms SignedBinaryQuinticSharpBound.nonnegative_model
#print axioms SignedBinaryQuinticSharpBound.real_model
#print axioms SignedBinaryQuinticSharpBound.real_coefficient_iff
#print axioms SignedBinaryQuinticSharpBound.nonnegative_coefficient_iff
#print axioms SignedBinaryQuinticSharpBound.signed_constant_gt_four
#print axioms SignedBinaryQuinticSharpBound.source_counterexample
#print axioms solution
