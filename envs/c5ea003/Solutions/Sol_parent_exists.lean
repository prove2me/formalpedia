-- Prove2me | solution 1 for parent_exists
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:22:16.03164+00:00
-- url     : https://prove2.me/submissions/d83b75cd-5d1e-43f0-91a5-7f82e89a23db

-- Sol generated from Bridges/BerggrenTrees/Parent_hyp_lt.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenTrees_Parent_hyp_lt

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-! ## Reconstructed definitions

`IsPT` is the Pythagorean relation, and `invB1`, `invB2`, `invB3` are the three
inverse Berggren maps (the parent maps of the Berggren ternary tree), i.e. the
inverses of the matrices `[[1,-2,2],[2,-1,2],[2,-2,3]]`, `[[1,2,2],[2,1,2],[2,2,3]]`
and `[[-1,2,2],[-2,1,2],[-2,2,3]]`. -/






/-- For a Pythagorean triple with positive legs the parent hypotenuse is positive. -/
theorem parent_hyp_pos' (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 0 < -2*a - 2*b + 3*c := by
  unfold IsPT at hpt
  nlinarith [sq_nonneg (3*c - 2*a - 2*b), sq_nonneg (a - b), mul_pos ha hb]

/-- If both `a + 2b > 2c` and `2a + b > 2c`, the branch-2 parent is positive. -/
theorem invB2_pos_case (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (h3 : a + 2 * b > 2 * c) (h4 : 2 * a + b > 2 * c) :
    0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2 := by
  refine ⟨by simp only [invB2]; omega, by simp only [invB2]; omega, ?_⟩
  simpa [invB2] using parent_hyp_pos' a b c ha hb hc hpt

/-- If `a + 2b > 2c` but `2a + b < 2c`, the branch-1 parent is positive. -/
theorem invB1_pos_case (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (h3 : a + 2 * b > 2 * c) (h4 : 2 * a + b < 2 * c) :
    0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2 := by
  refine ⟨by simp only [invB1]; omega, by simp only [invB1]; omega, ?_⟩
  simpa [invB1] using parent_hyp_pos' a b c ha hb hc hpt

/-- If `a + 2b < 2c` but `2a + b > 2c`, the branch-3 parent is positive. -/
theorem invB3_pos_case (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (h3 : a + 2 * b < 2 * c) (h4 : 2 * a + b > 2 * c) :
    0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2 := by
  refine ⟨by simp only [invB3]; omega, by simp only [invB3]; omega, ?_⟩
  simpa [invB3] using parent_hyp_pos' a b c ha hb hc hpt

/-- For a Pythagorean triple with positive legs, `a + 2b` and `2a + b` cannot both
be at most `2c`: otherwise `4b ≤ 3a` and `4a ≤ 3b`, forcing `b ≤ 0`. -/
theorem not_both_neg (a b c : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hpt : IsPT a b c) (h3 : a + 2 * b ≤ 2 * c) (h4 : 2 * a + b ≤ 2 * c) : False := by
  unfold IsPT at hpt
  have hc0 : 0 < c := by omega
  have e1 : (a + 2 * b) ^ 2 ≤ (2 * c) ^ 2 := by nlinarith
  have e2 : (2 * a + b) ^ 2 ≤ (2 * c) ^ 2 := by nlinarith
  have k1 : 4 * (a * b) ≤ 3 * a ^ 2 := by nlinarith
  have k2 : 4 * (a * b) ≤ 3 * b ^ 2 := by nlinarith
  nlinarith [mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a + b)]



theorem solution(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : c > 5) (hprim : Int.gcd a b = 1) :
    (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ∨
    (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ∨
    (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) := by
  by_cases h1 : a + 2 * b = 2 * c;
  · -- If $a + 2b = 2c$, then substituting $c = \frac{a + 2b}{2}$ into $a^2 + b^2 = c^2$ gives $3a^2 = 4ab$, so $3a = 4b$ (since $a > 0$).
    have h_eq : 3 * a = 4 * b := by
      unfold IsPT at hpt; nlinarith;
    -- Since $a$ and $b$ are coprime and $3a = 4b$, it follows that $a = 4k$ and $b = 3k$ for some integer $k$.
    obtain ⟨k, rfl, rfl⟩ : ∃ k : ℤ, a = 4 * k ∧ b = 3 * k := by
      exact ⟨ a / 4, by omega, by omega ⟩;
    simp_all +decide [ Int.gcd_mul_left, Int.gcd_mul_right ];
    grind;
  · by_cases h2 : 2 * a + b = 2 * c;
    · -- If $2a + b = 2c$, then substituting $c = (2a + b)/2$ into $a^2 + b^2 = c^2$ gives $3b^2 = 4ab$, so $3b = 4a$ (b>0). So $a = 3t$, $b = 4t$, $c = 5t$. Primitivity (gcd(a,b)=1) forces $t=1$, so $c=5$, contradicting $c > 5$.
      obtain ⟨t, ht⟩ : ∃ t : ℤ, a = 3 * t ∧ b = 4 * t ∧ c = 5 * t := by
        use a / 3;
        have h_eq : 3 * b = 4 * a := by
          nlinarith only [ ha, hb, hc, h2, hpt.symm ];
        omega;
      simp_all +decide [ Int.gcd_mul_left, Int.gcd_mul_right ];
      grind;
    · by_cases h3 : a + 2 * b > 2 * c <;> by_cases h4 : 2 * a + b > 2 * c;
      · exact Or.inr <| Or.inl <| invB2_pos_case a b c ha hb hc hpt h3 h4;
      · exact Or.inl <| invB1_pos_case a b c ha hb hc hpt h3 <| lt_of_le_of_ne ( le_of_not_gt h4 ) h2;
      · exact Or.inr <| Or.inr <| invB3_pos_case a b c ha hb hc hpt ( lt_of_le_of_ne ( le_of_not_gt h3 ) h1 ) h4;
      · exact False.elim <| not_both_neg a b c ha hb hpt ( le_of_not_gt h3 ) ( le_of_not_gt h4 )
