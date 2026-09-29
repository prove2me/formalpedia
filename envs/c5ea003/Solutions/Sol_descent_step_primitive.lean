-- Prove2me | solution 1 for descent_step_primitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:19.917443+00:00
-- url     : https://prove2.me/submissions/9e103aa0-88da-4ee8-b06c-1f649af6528f

-- Sol generated from Speculative/NumberTheory/BerggrenDescentComplete.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_BerggrenDescentComplete

/-! # CatalogBuild.Speculative.BerggrenDescentComplete

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 32
-/










theorem parent_hyp_shared'' (a b c : ℤ) (s : BerggrenStep') :
    (parentTriple' s (a, b, c)).2.2 = -2*a - 2*b + 3*c := by
  cases s <;> simp [parentTriple']


theorem parent_hyp_strict_decrease' (a b c : ℤ) (h : a^2 + b^2 = c^2)
    (ha : 0 < a) (hb : 0 < b) :
    -2*a - 2*b + 3*c < c := by
  nlinarith [mul_pos ha hb]




theorem parentA_preserves_pyth' (a b c : ℤ) (h : a^2 + b^2 = c^2) :
    (a + 2*b - 2*c)^2 + (-2*a - b + 2*c)^2 = (-2*a - 2*b + 3*c)^2 := by nlinarith [h]

theorem parentB_preserves_pyth' (a b c : ℤ) (h : a^2 + b^2 = c^2) :
    (a + 2*b - 2*c)^2 + (2*a + b - 2*c)^2 = (-2*a - 2*b + 3*c)^2 := by nlinarith [h]

theorem parentC_preserves_pyth' (a b c : ℤ) (h : a^2 + b^2 = c^2) :
    (-a - 2*b + 2*c)^2 + (2*a + b - 2*c)^2 = (-2*a - 2*b + 3*c)^2 := by nlinarith [h]



theorem not_both_sigma_nonpos' (a b c : ℤ) (h : a^2 + b^2 = c^2)
    (ha : 0 < a) (hb : 0 < b) :
    ¬(sigma1' a b c ≤ 0 ∧ sigma2' a b c ≤ 0) := by
  unfold sigma1' sigma2'; intro ⟨h1, h2⟩
  nlinarith [sq_nonneg (a - b), mul_pos ha hb]


/-- When σ₁ > 0 and σ₂ > 0, parentB has all positive components -/
theorem parentB_positive_when' (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 = c^2)
    (hs1 : 0 < sigma1' a b c) (hs2 : 0 < sigma2' a b c) :
    0 < (parentTriple' .B (a, b, c)).1 ∧
    0 < (parentTriple' .B (a, b, c)).2.1 ∧
    0 < (parentTriple' .B (a, b, c)).2.2 := by
  simp [parentTriple', sigma1', sigma2'] at *
  exact ⟨by linarith, by linarith, by nlinarith [sq_nonneg (a - b), mul_pos ha hb]⟩

/-- When σ₁ > 0 and σ₂ < 0, parentA has all positive components -/
theorem parentA_positive_when' (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 = c^2)
    (hs1 : 0 < sigma1' a b c) (hs2 : sigma2' a b c < 0) :
    0 < (parentTriple' .A (a, b, c)).1 ∧
    0 < (parentTriple' .A (a, b, c)).2.1 ∧
    0 < (parentTriple' .A (a, b, c)).2.2 := by
  simp [parentTriple', sigma1', sigma2'] at *
  exact ⟨by linarith, by linarith, by nlinarith [sq_nonneg (a - b), mul_pos ha hb]⟩

/-- When σ₁ < 0 and σ₂ > 0, parentC has all positive components -/
theorem parentC_positive_when' (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 = c^2)
    (hs1 : sigma1' a b c < 0) (hs2 : 0 < sigma2' a b c) :
    0 < (parentTriple' .C (a, b, c)).1 ∧
    0 < (parentTriple' .C (a, b, c)).2.1 ∧
    0 < (parentTriple' .C (a, b, c)).2.2 := by
  simp [parentTriple', sigma1', sigma2'] at *
  exact ⟨by linarith, by linarith, by nlinarith [sq_nonneg (a - b), mul_pos ha hb]⟩



theorem sigma1_nonzero_primitive (a b c : ℤ) (h : a^2 + b^2 = c^2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc5 : 5 < c)
    (hcop : Int.gcd a b = 1) :
    sigma1' a b c ≠ 0 := by
  -- Assume σ₁ = 0, i.e., a + 2b = 2c. Combined with a² + b² = c², substitute c = (a+2b)/2 to get 4a² + 4b² = (a+2b)² = a² + 4ab + 4b², hence 3a² = 4ab, so 3a = 4b (since a > 0). Then a = 4k, b = 3k for some positive integer k, and c = (4k + 6k)/2 = 5k. Since Int.gcd a b = Int.gcd (4k) (3k) = k * gcd(4,3) = k, and hcop says gcd = 1, we get k = 1, so c = 5. But hc5 says 5 < c, contradiction.
  by_contra h_sigma1_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a = 4 * k ∧ b = 3 * k := by
    have h_eq : 3 * a = 4 * b := by
      unfold sigma1' at h_sigma1_zero; nlinarith;
    exact ⟨ a / 4, by omega, by omega ⟩;
  simp_all +decide [ Int.gcd_mul_left ];
  norm_num [ Int.gcd_mul_left, Int.gcd_mul_right ] at hcop;
  nlinarith only [ h, hc5, ha, abs_of_pos ha, hcop ]

theorem sigma2_nonzero_primitive (a b c : ℤ) (h : a^2 + b^2 = c^2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc5 : 5 < c)
    (hcop : Int.gcd a b = 1) :
    sigma2' a b c ≠ 0 := by
  by_contra h_sigma2_zero;
  -- If σ₁ = 0 and σ₂ = 0, then 3a = 4b (by nlinarith [sq_nonneg (4*a - 3*b)]).
  have h_ab_eq : 4 * a = 3 * b := by
    unfold sigma2' at h_sigma2_zero;
    nlinarith only [ ha, hb, hc5, h, h_sigma2_zero ];
  -- From 4a = 3b, we deduce that b = 4k and a = 3k for some integer k.
  obtain ⟨k, rfl, rfl⟩ : ∃ k : ℤ, b = 4 * k ∧ a = 3 * k := by
    exact ⟨ b / 4, by omega, by omega ⟩;
  norm_num [ Int.gcd_mul_left, Int.gcd_mul_right ] at hcop;
  nlinarith [ abs_of_pos ( by linarith : 0 < k ) ]





theorem solution(a b c : ℤ) (h : a^2 + b^2 = c^2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc5 : 5 < c)
    (hcop : Int.gcd a b = 1) :
    ∃ (s : BerggrenStep'),
      let p := parentTriple' s (a, b, c)
      0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.2 < c ∧
      p.1^2 + p.2.1^2 = p.2.2^2 := by
  have hs1_ne := sigma1_nonzero_primitive a b c h ha hb hc hc5 hcop
  have hs2_ne := sigma2_nonzero_primitive a b c h ha hb hc hc5 hcop
  -- Now σ₁ and σ₂ are both nonzero
  by_cases hs1 : sigma1' a b c < 0
  · have hs2 : 0 < sigma2' a b c := by
      rcases lt_or_gt_of_ne hs2_ne with hlt | hgt
      · exfalso; exact not_both_sigma_nonpos' a b c h ha hb ⟨le_of_lt hs1, le_of_lt hlt⟩
      · exact hgt
    exact ⟨.C, by
      obtain ⟨h1, h2, h3⟩ := parentC_positive_when' a b c ha hb hc h hs1 hs2
      refine ⟨h1, h2, h3, ?_, parentC_preserves_pyth' a b c h⟩
      rw [parent_hyp_shared'']
      linarith [parent_hyp_strict_decrease' a b c h ha hb]⟩
  · push_neg at hs1
    have hs1_pos : 0 < sigma1' a b c := lt_of_le_of_ne hs1 (Ne.symm hs1_ne)
    by_cases hs2 : sigma2' a b c < 0
    · exact ⟨.A, by
        obtain ⟨h1, h2, h3⟩ := parentA_positive_when' a b c ha hb hc h hs1_pos hs2
        refine ⟨h1, h2, h3, ?_, parentA_preserves_pyth' a b c h⟩
        rw [parent_hyp_shared'']
        linarith [parent_hyp_strict_decrease' a b c h ha hb]⟩
    · push_neg at hs2
      have hs2_pos : 0 < sigma2' a b c := lt_of_le_of_ne hs2 (Ne.symm hs2_ne)
      exact ⟨.B, by
        obtain ⟨h1, h2, h3⟩ := parentB_positive_when' a b c ha hb hc h hs1_pos hs2_pos
        refine ⟨h1, h2, h3, ?_, parentB_preserves_pyth' a b c h⟩
        rw [parent_hyp_shared'']
        linarith [parent_hyp_strict_decrease' a b c h ha hb]⟩
