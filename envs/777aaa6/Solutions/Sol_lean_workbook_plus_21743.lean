-- Prove2me | solution 1 for lean_workbook_plus_21743
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:06:57.005478+00:00
-- url     : https://prove2.me/submissions/77e411e0-64b0-40e7-bfcd-1239de67ac0c

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable def sphereReciprocalValue (x y z : ℝ) : ℝ :=
  x/(1+y*z)+y/(1+x*z)+z/(1+x*y)

def positiveSphereValues : Set ℝ :=
  {v | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x^2+y^2+z^2 = 1 ∧ sphereReciprocalValue x y z = v}

theorem sphere_coordinate_product_lt_one (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hs : x^2+y^2+z^2 = 1) : x+x*y*z < 1 := by
  have hx1 : x < 1 := by nlinarith [sq_pos_of_pos hy, sq_nonneg z]
  have hpos := mul_pos (sq_pos_of_pos (sub_pos.mpr hx1)) (show 0 < x+2 by linarith)
  have hnonneg := mul_nonneg hx.le (sq_nonneg (y-z))
  have heq : 2*(1-x-x*y*z) = (1-x)^2*(x+2)+x*(y-z)^2 := by
    nlinarith [congrArg (fun t : ℝ => x*t) hs]
  nlinarith

theorem sphere_reciprocal_coordinate_gt_square (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : x^2+y^2+z^2 = 1) :
    x^2 < x/(1+y*z) := by
  have hden : 0 < 1+y*z := by positivity
  apply (lt_div_iff₀ hden).mpr
  have h := sphere_coordinate_product_lt_one x y z hx hy hz hs
  nlinarith [mul_pos hx (sub_pos.mpr h)]

theorem sphere_reciprocal_strict_lower (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : x^2+y^2+z^2 = 1) :
    1 < sphereReciprocalValue x y z := by
  have h1 := sphere_reciprocal_coordinate_gt_square x y z hx hy hz hs
  have h2 := sphere_reciprocal_coordinate_gt_square y x z hy hx hz (by nlinarith only [hs])
  have h3 := sphere_reciprocal_coordinate_gt_square z x y hz hx hy (by nlinarith only [hs])
  unfold sphereReciprocalValue
  linarith

-- The ordered Schur certificate is also used in the archive's earlier Schur result.
theorem sphere_schur_ordered (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    a^2*(b+c-a)+b^2*(a+c-b)+c^2*(a+b-c) ≤ 3*a*b*c := by
  have h1 := mul_nonneg (sq_nonneg (a-b)) (show 0 ≤ a+b-c by linarith)
  have h2 := mul_nonneg hc (mul_nonneg (sub_nonneg.mpr (hbc.trans hab)) (sub_nonneg.mpr hbc))
  nlinarith

theorem sphere_schur (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x^2+y^2+z^2 = 1) : (x+y+z)*((x+y+z)^2-2) ≤ 9*x*y*z := by
  have h : x^2*(y+z-x)+y^2*(x+z-y)+z^2*(x+y-z) ≤ 3*x*y*z := by
    rcases le_total x y with hxy | hyx
    · rcases le_total y z with hyz | hzy
      · nlinarith [sphere_schur_ordered z y x hx hyz hxy]
      · rcases le_total x z with hxz | hzx
        · nlinarith [sphere_schur_ordered y z x hx hzy hxz]
        · nlinarith [sphere_schur_ordered y x z hz hxy hzx]
    · rcases le_total x z with hxz | hzx
      · nlinarith [sphere_schur_ordered z x y hy hxz hyx]
      · rcases le_total y z with hyz | hzy
        · nlinarith [sphere_schur_ordered x z y hy hzx hyz]
        · exact sphere_schur_ordered x y z hz hyx hzy
  nlinarith [congrArg (fun t : ℝ => (x+y+z)*t) hs]

theorem positive_reciprocal_cauchy (A B C : ℝ) (ha : 0 < A) (hb : 0 < B) (hc : 0 < C) :
    9 ≤ (1/A+1/B+1/C)*(A+B+C) := by
  apply (mul_le_mul_iff_left₀ (mul_pos (mul_pos ha hb) hc)).mp
  calc
    9*(A*B*C) ≤ (A+B+C)*(A*B+A*C+B*C) := by
      nlinarith [mul_nonneg hc.le (sq_nonneg (A-B)),
        mul_nonneg ha.le (sq_nonneg (B-C)), mul_nonneg hb.le (sq_nonneg (C-A))]
    _ = (1/A+1/B+1/C)*(A+B+C)*(A*B*C) := by
      field_simp <;> ring

theorem sphere_reciprocal_identity (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    sphereReciprocalValue x y z = (x+y+z) - x*y*z*(1/(1+y*z)+1/(1+x*z)+1/(1+x*y)) := by
  have h1 : 1+y*z ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1+x*z ≠ 0 := ne_of_gt (by positivity)
  have h3 : 1+x*y ≠ 0 := ne_of_gt (by positivity)
  unfold sphereReciprocalValue
  field_simp <;> ring

theorem sphere_sum_reciprocal_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x^2+y^2+z^2 = 1) :
    18 ≤ (1/(1+y*z)+1/(1+x*z)+1/(1+x*y))*((x+y+z)^2+5) := by
  have h := positive_reciprocal_cauchy (1+y*z) (1+x*z) (1+x*y)
    (by positivity) (by positivity) (by positivity)
  have heq : (x+y+z)^2+5 = 2*((1+y*z)+(1+x*z)+(1+x*y)) := by nlinarith only [hs]
  rw [heq]
  nlinarith only [h]

theorem sphere_cubic_gap (p : ℝ) (hp : Real.sqrt 2 < p) :
    p*(9-p^2) < Real.sqrt 2*(p^2+5) := by
  let s := Real.sqrt 2
  have hs : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have ht : 0 < p-s := sub_pos.mpr hp
  have heq : s*(p^2+5)-p*(9-p^2) =
      (p-s)*(1+4*s*(p-s)+(p-s)^2) := by
    calc
      _ = (p-s)*(1+4*s*(p-s)+(p-s)^2)+(s^2-2)*(5*p-3*s) := by ring
      _ = _ := by rw [hs]; ring
  have hpos : 0 < (p-s)*(1+4*s*(p-s)+(p-s)^2) := by positivity
  change p*(9-p^2) < s*(p^2+5)
  linarith

theorem sphere_reciprocal_strict_upper (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : x^2+y^2+z^2 = 1) :
    sphereReciprocalValue x y z < Real.sqrt 2 := by
  let p := x+y+z
  let r := x*y*z
  let T := 1/(1+y*z)+1/(1+x*z)+1/(1+x*y)
  have hr : 0 < r := by dsimp [r]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hF : sphereReciprocalValue x y z = p-r*T := sphere_reciprocal_identity x y z hx.le hy.le hz.le
  by_cases hp : p ≤ Real.sqrt 2
  · have hlt : sphereReciprocalValue x y z < p := by rw [hF]; nlinarith [mul_pos hr hT]
    exact hlt.trans_le hp
  · have hschur : p*(p^2-2) ≤ 9*r := by
      simpa only [p,r,mul_assoc] using sphere_schur x y z hx.le hy.le hz.le hs
    have hcauchy : 18 ≤ T*(p^2+5) := sphere_sum_reciprocal_bound x y z hx.le hy.le hz.le hs
    have hm := mul_le_mul_of_nonneg_left hcauchy hr.le
    have hprod : sphereReciprocalValue x y z*(p^2+5) ≤ p*(9-p^2) := by
      rw [hF]
      nlinarith only [hm,hschur]
    have hgap := sphere_cubic_gap p (lt_of_not_ge hp)
    exact (mul_lt_mul_iff_left₀ (show 0 < p^2+5 by positivity)).mp (hprod.trans_lt hgap)

noncomputable def spherePathDenom (t : ℝ) : ℝ := Real.sqrt (1+t^2+(t*(1-t))^2)
noncomputable def spherePathX (t : ℝ) : ℝ := 1/spherePathDenom t
noncomputable def spherePathY (t : ℝ) : ℝ := t/spherePathDenom t
noncomputable def spherePathZ (t : ℝ) : ℝ := t*(1-t)/spherePathDenom t
noncomputable def spherePathValue (t : ℝ) : ℝ :=
  sphereReciprocalValue (spherePathX t) (spherePathY t) (spherePathZ t)

theorem spherePathDenom_pos (t : ℝ) : 0 < spherePathDenom t := by
  apply Real.sqrt_pos.mpr
  positivity

theorem spherePath_normalized (t : ℝ) :
    spherePathX t^2+spherePathY t^2+spherePathZ t^2 = 1 := by
  have hq : 0 < 1+t^2+(t*(1-t))^2 := by positivity
  have hd : spherePathDenom t^2 = 1+t^2+(t*(1-t))^2 := Real.sq_sqrt hq.le
  simp only [spherePathX,spherePathY,spherePathZ,div_pow,one_pow,← add_div,hd,div_self hq.ne']

theorem spherePath_nonneg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ spherePathX t ∧ 0 ≤ spherePathY t ∧ 0 ≤ spherePathZ t := by
  have hd := (spherePathDenom_pos t).le
  exact ⟨div_nonneg (by norm_num) hd, div_nonneg ht.1 hd,
    div_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) hd⟩

theorem spherePath_pos (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    0 < spherePathX t ∧ 0 < spherePathY t ∧ 0 < spherePathZ t := by
  have hd := spherePathDenom_pos t
  exact ⟨div_pos (by norm_num) hd, div_pos ht.1 hd,
    div_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) hd⟩

theorem spherePathDenom_continuous : Continuous spherePathDenom := by
  unfold spherePathDenom
  fun_prop

theorem spherePathX_continuous : Continuous spherePathX :=
  continuous_const.div spherePathDenom_continuous (fun t => (spherePathDenom_pos t).ne')

theorem spherePathY_continuous : Continuous spherePathY :=
  continuous_id.div spherePathDenom_continuous (fun t => (spherePathDenom_pos t).ne')

theorem spherePathZ_continuous : Continuous spherePathZ :=
  (continuous_id.mul (continuous_const.sub continuous_id)).div spherePathDenom_continuous
    (fun t => (spherePathDenom_pos t).ne')

theorem spherePathValue_continuousOn : ContinuousOn spherePathValue (Set.Icc (0:ℝ) 1) := by
  have h1 : ∀ t ∈ Set.Icc (0:ℝ) 1, 1+spherePathY t*spherePathZ t ≠ 0 := by
    intro t ht
    obtain ⟨hx,hy,hz⟩ := spherePath_nonneg t ht
    positivity
  have h2 : ∀ t ∈ Set.Icc (0:ℝ) 1, 1+spherePathX t*spherePathZ t ≠ 0 := by
    intro t ht
    obtain ⟨hx,hy,hz⟩ := spherePath_nonneg t ht
    positivity
  have h3 : ∀ t ∈ Set.Icc (0:ℝ) 1, 1+spherePathX t*spherePathY t ≠ 0 := by
    intro t ht
    obtain ⟨hx,hy,hz⟩ := spherePath_nonneg t ht
    positivity
  exact ((spherePathX_continuous.continuousOn.div
    (continuous_const.add (spherePathY_continuous.mul spherePathZ_continuous)).continuousOn h1).add
    (spherePathY_continuous.continuousOn.div
      (continuous_const.add (spherePathX_continuous.mul spherePathZ_continuous)).continuousOn h2)).add
    (spherePathZ_continuous.continuousOn.div
      (continuous_const.add (spherePathX_continuous.mul spherePathY_continuous)).continuousOn h3)

theorem spherePathValue_zero : spherePathValue 0 = 1 := by
  simp only [spherePathValue,sphereReciprocalValue,spherePathX,spherePathY,spherePathZ,
    spherePathDenom,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,add_zero,
    sub_zero,Real.sqrt_one,div_one,zero_div]

theorem spherePathValue_one : spherePathValue 1 = Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hd : spherePathDenom 1 = Real.sqrt 2 := by
    unfold spherePathDenom
    congr 1
    ring
  simp only [spherePathValue,sphereReciprocalValue,spherePathX,spherePathY,spherePathZ,
    hd,sub_self,mul_zero,zero_div,add_zero,div_one]
  rw [← add_div,one_add_one_eq_two]
  exact (div_eq_iff hn).mpr (by simpa only [pow_two] using hs.symm)

theorem one_lt_sqrt_two : (1:ℝ) < Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem positiveSphereValues_eq : positiveSphereValues = Set.Ioo 1 (Real.sqrt 2) := by
  ext v
  constructor
  · rintro ⟨x,y,z,hx,hy,hz,hs,hv⟩
    rw [← hv]
    exact ⟨sphere_reciprocal_strict_lower x y z hx hy hz hs,
      sphere_reciprocal_strict_upper x y z hx hy hz hs⟩
  · intro hv
    have hv' : v ∈ Set.Icc (spherePathValue 0) (spherePathValue 1) := by
      rw [spherePathValue_zero,spherePathValue_one]
      exact ⟨hv.1.le,hv.2.le⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
      spherePathValue_continuousOn hv'
    have ht0 : t ≠ 0 := by
      intro h
      rw [h,spherePathValue_zero] at he
      linarith [hv.1]
    have ht1 : t ≠ 1 := by
      intro h
      rw [h,spherePathValue_one] at he
      linarith [hv.2]
    have htp : t ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩
    obtain ⟨hx,hy,hz⟩ := spherePath_pos t htp
    exact ⟨spherePathX t,spherePathY t,spherePathZ t,hx,hy,hz,spherePath_normalized t,he⟩

theorem positiveSphereValues_infimum : sInf positiveSphereValues = 1 := by
  rw [positiveSphereValues_eq]
  exact csInf_Ioo one_lt_sqrt_two

theorem positiveSphereValues_supremum : sSup positiveSphereValues = Real.sqrt 2 := by
  rw [positiveSphereValues_eq]
  exact csSup_Ioo one_lt_sqrt_two

theorem positiveSphereValues_endpoints_not_attained :
    (1:ℝ) ∉ positiveSphereValues ∧ Real.sqrt 2 ∉ positiveSphereValues := by
  rw [positiveSphereValues_eq]
  simp

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (hx2 : x^2+y^2+z^2 = 1) :
    (x/(1+y*z)+y/(1+x*z)+z/(1+x*y) ≤ 1 ∨
     x/(1+y*z)+y/(1+x*z)+z/(1+x*y) ≥ 1) :=
  Or.inr (sphere_reciprocal_strict_lower x y z hx hy hz hx2).le

#print axioms sphereReciprocalValue
#print axioms positiveSphereValues
#print axioms sphere_coordinate_product_lt_one
#print axioms sphere_reciprocal_coordinate_gt_square
#print axioms sphere_reciprocal_strict_lower
#print axioms sphere_schur_ordered
#print axioms sphere_schur
#print axioms positive_reciprocal_cauchy
#print axioms sphere_reciprocal_identity
#print axioms sphere_sum_reciprocal_bound
#print axioms sphere_cubic_gap
#print axioms sphere_reciprocal_strict_upper
#print axioms spherePathDenom
#print axioms spherePathX
#print axioms spherePathY
#print axioms spherePathZ
#print axioms spherePathValue
#print axioms spherePathDenom_pos
#print axioms spherePath_normalized
#print axioms spherePath_nonneg
#print axioms spherePath_pos
#print axioms spherePathDenom_continuous
#print axioms spherePathX_continuous
#print axioms spherePathY_continuous
#print axioms spherePathZ_continuous
#print axioms spherePathValue_continuousOn
#print axioms spherePathValue_zero
#print axioms spherePathValue_one
#print axioms one_lt_sqrt_two
#print axioms positiveSphereValues_eq
#print axioms positiveSphereValues_infimum
#print axioms positiveSphereValues_supremum
#print axioms positiveSphereValues_endpoints_not_attained
#print axioms solution
