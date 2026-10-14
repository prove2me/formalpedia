-- Prove2me | solution 1 for Thurston23.isKleinian_gammaSeven
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-14T16:24:20.70763+00:00
-- url     : https://prove2.me/submissions/c5020064-d8cb-4730-a466-8903a38f380c

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_eisenstein

/-!
`Γ(3 + ω)` is a Kleinian group. Verbatim from the mission's source files: the general bounds of the
Picard section of `Thurston23.lean`, and the sections `EisGroup` and `EisCongruence` of
`Thurston23Eisenstein.lean`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

section ReusedA

open MatrixGroups Quaternion

theorem normSq_coeComplex (z : ℂ) : normSq (z : ℍ) = Complex.normSq z := by
  simp only [normSq_def', re_coeComplex, imI_coeComplex, imJ_coeComplex, imK_coeComplex,
    Complex.normSq_apply]
  ring

/-- `|x + y|² ≤ 2 (|x|² + |y|²)` in the quaternions. -/
theorem normSq_add_le (x y : ℍ) : normSq (x + y) ≤ 2 * (normSq x + normSq y) := by
  simp only [normSq_def', Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.imI - y.imI), sq_nonneg (x.imJ - y.imJ),
    sq_nonneg (x.imK - y.imK)]

/-- On the half-space `|c q + d|² ≥ |c|² t²`: the `j` and `k` parts of `c q + d` are `c t`. -/
theorem normSq_mul_imJ_le (c d : ℂ) {q : ℍ} (hK : q.imK = 0) :
    Complex.normSq c * q.imJ ^ 2 ≤ normSq ((c : ℍ) * q + (d : ℍ)) := by
  simp [normSq_def', hK, Complex.normSq_apply]
  nlinarith [sq_nonneg (c.re * q.re - c.im * q.imI + d.re),
    sq_nonneg (c.re * q.imI + c.im * q.re + d.im)]

/-- A compact subset of `ℍ³` lies in a box: heights in `[t₀, T]` with `t₀ > 0`, and
`|q|² ≤ R`. -/
theorem exists_box_of_isCompact {K : Set H3} (hK : IsCompact K) :
    ∃ t₀ T R : ℝ, 0 < t₀ ∧ ∀ p ∈ K, t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 0, 0, one_pos, by simp⟩
  have hh : Continuous fun p : H3 => p.1 2 := (continuous_apply 2).comp continuous_subtype_val
  have hn : Continuous fun p : H3 => normSq (toQ p) := by
    have : (fun p : H3 => normSq (toQ p)) = fun p => ‖toQ p‖ * ‖toQ p‖ :=
      funext fun p => normSq_eq_norm_mul_self _
    rw [this]
    exact (continuous_norm.comp continuous_toQ).mul (continuous_norm.comp continuous_toQ)
  obtain ⟨p₀, -, hmin⟩ := hK.exists_isMinOn hne hh.continuousOn
  obtain ⟨T, hT⟩ := hK.bddAbove_image hh.continuousOn
  obtain ⟨R, hR⟩ := hK.bddAbove_image hn.continuousOn
  exact ⟨p₀.1 2, T, R, p₀.2, fun p hp => ⟨hmin hp, hT ⟨p, hp, rfl⟩, hR ⟨p, hp, rfl⟩⟩⟩

/-- The height of `g • p` is the height of `p` divided by `|c q + d|²`. -/
theorem smul_height (g : SL(2, ℂ)) (p : H3) :
    (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
  (mobiusQ_imJ g (toQ_imK p)).1

/-- If `g` moves a point of the box to a point of the box, then `|c q + d|² ≤ T / t₀`, so
`|c|² ≤ T / t₀³` and `|d|² ≤ 2 (T / t₀ + R T / t₀³)`. -/
theorem bottom_row_bound (g : SL(2, ℂ)) {t₀ T R : ℝ} (ht₀ : 0 < t₀) {p : H3}
    (hp : t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R)
    (hgp : t₀ ≤ (g • p).1 2 ∧ (g • p).1 2 ≤ T ∧ normSq (toQ (g • p)) ≤ R) :
    normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ T / t₀ ∧
      Complex.normSq (g 1 0) ≤ T / t₀ / t₀ ^ 2 ∧
      Complex.normSq (g 1 1) ≤ 2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) := by
  have hh := smul_height g p
  have hMpos := normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hc := normSq_mul_imJ_le (g 1 0) (g 1 1) (toQ_imK p)
  rw [show (toQ p).imJ = p.1 2 from rfl] at hc
  generalize hM : ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) = M at hh hMpos hc ⊢
  have hM0 : normSq M ≠ 0 := hMpos.ne'
  -- the denominator
  have hD : normSq M ≤ T / t₀ := by
    rw [le_div_iff₀ ht₀]
    have e : normSq M * (g • p).1 2 = p.1 2 := by rw [hh]; field_simp
    linarith [mul_le_mul_of_nonneg_left hgp.1 hMpos.le, hp.2.1]
  -- the entry `c`
  have ht2 : t₀ ^ 2 ≤ p.1 2 ^ 2 := by nlinarith [mul_le_mul hp.1 hp.1 ht₀.le (ht₀.le.trans hp.1)]
  have hcb : Complex.normSq (g 1 0) ≤ T / t₀ / t₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_left ht2 (Complex.normSq_nonneg (g 1 0))]
  -- the entry `d = (c q + d) − c q`
  have hd : ((g 1 1 : ℂ) : ℍ) = M + -(((g 1 0 : ℂ) : ℍ) * toQ p) := by rw [← hM]; abel
  have hdb := normSq_add_le M (-(((g 1 0 : ℂ) : ℍ) * toQ p))
  rw [← hd, normSq_neg, map_mul, normSq_coeComplex, normSq_coeComplex] at hdb
  have hcq : Complex.normSq (g 1 0) * normSq (toQ p) ≤ T / t₀ / t₀ ^ 2 * R :=
    mul_le_mul hcb hp.2.2 normSq_nonneg ((Complex.normSq_nonneg _).trans hcb)
  exact ⟨hD, hcb, by linarith⟩

/-- The bound on every entry produced by `entries_bound`. -/
noncomputable def entryBound (t₀ T R : ℝ) : ℝ :=
  max (T / t₀ / t₀ ^ 2) (max (2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R))
    (2 * (R * (T / t₀) + 2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) * R)))

/-- If `g` moves a point of the box to a point of the box, every entry of `g` is bounded in
terms of the box alone. -/
theorem entries_bound (g : SL(2, ℂ)) {t₀ T R : ℝ} (ht₀ : 0 < t₀) {p : H3}
    (hp : t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R)
    (hgp : t₀ ≤ (g • p).1 2 ∧ (g • p).1 2 ≤ T ∧ normSq (toQ (g • p)) ≤ R) :
    ∀ i j, Complex.normSq (g i j) ≤ entryBound t₀ T R := by
  obtain ⟨hD, hc, hd⟩ := bottom_row_bound g ht₀ hp hgp
  -- `g⁻¹ = !![d, -b; -c, a]` moves `g • p` back to `p`, so its bottom row bounds `a`
  have hinv := bottom_row_bound g⁻¹ ht₀ hgp (by rw [inv_smul_smul]; exact hp)
  have h11 : (g⁻¹) 1 1 = g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have ha := hinv.2.2
  rw [h11] at ha
  -- `b = (g q)(c q + d) − a q`
  have hM0 := denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2
  have hid : ((g 0 1 : ℂ) : ℍ) =
      toQ (g • p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) +
        -(((g 0 0 : ℂ) : ℍ) * toQ p) := by
    rw [toQ_smul]
    unfold mobiusQ
    rw [inv_mul_cancel_right₀ hM0]
    abel
  have hbb := normSq_add_le (toQ (g • p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)))
    (-(((g 0 0 : ℂ) : ℍ) * toQ p))
  rw [← hid, normSq_neg, map_mul, map_mul, normSq_coeComplex, normSq_coeComplex] at hbb
  have hR : 0 ≤ R := normSq_nonneg.trans hp.2.2
  have h1 : normSq (toQ (g • p)) * normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤
      R * (T / t₀) := mul_le_mul hgp.2.2 hD normSq_nonneg hR
  have h2 : Complex.normSq (g 0 0) * normSq (toQ p) ≤
      2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) * R :=
    mul_le_mul ha hp.2.2 normSq_nonneg ((Complex.normSq_nonneg _).trans ha)
  have hb : Complex.normSq (g 0 1) ≤ 2 * (R * (T / t₀) + 2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) * R) := by
    linarith
  unfold entryBound
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · exact le_max_of_le_right (le_max_of_le_left ha)
  · exact le_max_of_le_right (le_max_of_le_right hb)
  · exact le_max_of_le_left hc
  · exact le_max_of_le_right (le_max_of_le_left hd)

end ReusedA

section ReusedB

open MatrixGroups Quaternion

/-- The real algebra at a fixed point. The variables are the coordinates of `q = x + y i + t j`
and the real and imaginary parts of the entries; the hypotheses are the four components of
`q (c q + d) = a q + b` and `|c q + d|² = 1`. -/
theorem fixed_point_real (x y t a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℝ) (ht : 0 < t)
    (e₀ : x * (c₁ * x - c₂ * y + d₁) - y * (c₁ * y + c₂ * x + d₂) - t * (c₁ * t) =
      a₁ * x - a₂ * y + b₁)
    (e₁ : x * (c₁ * y + c₂ * x + d₂) + y * (c₁ * x - c₂ * y + d₁) + t * (c₂ * t) =
      a₁ * y + a₂ * x + b₂)
    (e₂ : t * (2 * (c₁ * x - c₂ * y) + d₁) = a₁ * t)
    (e₃ : -(t * d₂) = a₂ * t)
    (hN : (c₁ * x - c₂ * y + d₁) ^ 2 + (c₁ * y + c₂ * x + d₂) ^ 2 + (c₁ * t) ^ 2 +
      (c₂ * t) ^ 2 = 1) :
    a₂ + d₂ = 0 ∧ -2 ≤ a₁ + d₁ ∧ a₁ + d₁ ≤ 2 ∧
      (a₁ + d₁ = 2 →
        a₁ = 1 ∧ a₂ = 0 ∧ b₁ = 0 ∧ b₂ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ d₁ = 1 ∧ d₂ = 0) := by
  have ht0 : t ≠ 0 := ht.ne'
  have ha₁ : a₁ = 2 * (c₁ * x - c₂ * y) + d₁ :=
    mul_right_cancel₀ ht0 (by linear_combination (-1 : ℝ) * e₂)
  have ha₂ : a₂ = -d₂ := mul_right_cancel₀ ht0 (by linear_combination (-1 : ℝ) * e₃)
  have htr : a₁ + d₁ = 2 * (c₁ * x - c₂ * y + d₁) := by linear_combination ha₁
  have hm : (c₁ * x - c₂ * y + d₁) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (c₁ * y + c₂ * x + d₂), sq_nonneg (c₁ * t), sq_nonneg (c₂ * t)]
  refine ⟨by linear_combination ha₂, by nlinarith [sq_nonneg (c₁ * x - c₂ * y + d₁ + 1)],
    by nlinarith [sq_nonneg (c₁ * x - c₂ * y + d₁ - 1)], fun h2 => ?_⟩
  have hm1 : c₁ * x - c₂ * y + d₁ = 1 := by linarith
  have hS : (c₁ * y + c₂ * x + d₂) ^ 2 + (c₁ * t) ^ 2 + (c₂ * t) ^ 2 = 0 := by
    linear_combination hN - (c₁ * x - c₂ * y + d₁ + 1) * hm1
  have hc₁ : c₁ = 0 := by
    have h : (c₁ * t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (c₁ * y + c₂ * x + d₂), sq_nonneg (c₁ * t), sq_nonneg (c₂ * t)]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)).resolve_right ht0
  have hc₂ : c₂ = 0 := by
    have h : (c₂ * t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (c₁ * y + c₂ * x + d₂), sq_nonneg (c₁ * t), sq_nonneg (c₂ * t)]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)).resolve_right ht0
  subst hc₁ hc₂
  have hd₁ : d₁ = 1 := by linear_combination hm1
  have hd₂ : d₂ = 0 := (pow_eq_zero_iff two_ne_zero).1 (by linear_combination hS)
  subst hd₁ hd₂
  have ha₁' : a₁ = 1 := by linear_combination ha₁
  have ha₂' : a₂ = 0 := by linear_combination ha₂
  subst ha₁' ha₂'
  exact ⟨rfl, rfl, by linear_combination (-1 : ℝ) * e₀, by linear_combination (-1 : ℝ) * e₁,
    rfl, rfl, rfl, rfl⟩

/-- At a fixed point of `g` the trace is real and lies in `[-2, 2]`, and it is `2` only for
`g = 1`. -/
theorem fixed_point_trace (g : SL(2, ℂ)) (p : H3) (hfix : g • p = p) :
    (g 0 0 + g 1 1).im = 0 ∧ -2 ≤ (g 0 0 + g 1 1).re ∧ (g 0 0 + g 1 1).re ≤ 2 ∧
      (g 0 0 + g 1 1 = 2 → g = 1) := by
  have hK := toQ_imK p
  have hM0 := denom_ne_zero (sl2_row_ne_zero g) hK p.2
  -- `q (c q + d) = a q + b`
  have hq : toQ p * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) =
      ((g 0 0 : ℂ) : ℍ) * toQ p + ((g 0 1 : ℂ) : ℍ) := by
    have e : mobiusQ g (toQ p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) =
        ((g 0 0 : ℂ) : ℍ) * toQ p + ((g 0 1 : ℂ) : ℍ) := by
      unfold mobiusQ
      exact inv_mul_cancel_right₀ hM0 _
    rwa [← toQ_smul, hfix] at e
  -- `|c q + d|² = 1`, since the height is unchanged
  have hN : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) = 1 := by
    have hh := smul_height g p
    rw [hfix, eq_div_iff (normSq_pos hM0).ne'] at hh
    exact mul_left_cancel₀ p.2.ne' (hh.trans (mul_one _).symm)
  have e₀ := congrArg QuaternionAlgebra.re hq
  have e₁ := congrArg QuaternionAlgebra.imI hq
  have e₂ := congrArg QuaternionAlgebra.imJ hq
  have e₃ := congrArg QuaternionAlgebra.imK hq
  rw [normSq_def'] at hN
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    re_coeComplex, imI_coeComplex, imJ_coeComplex, imK_coeComplex, hK] at e₀ e₁ e₂ e₃ hN
  obtain ⟨h1, h2, h3, h4⟩ := fixed_point_real (toQ p).re (toQ p).imI (toQ p).imJ
    (g 0 0).re (g 0 0).im (g 0 1).re (g 0 1).im (g 1 0).re (g 1 0).im (g 1 1).re (g 1 1).im
    (toQ_imJ_pos p) (by linear_combination e₀) (by linear_combination e₁)
    (by linear_combination e₂) (by linear_combination e₃) (by linear_combination hN)
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, fun htr => ?_⟩
  have htr' : (g 0 0).re + (g 1 1).re = 2 := by simpa using congrArg Complex.re htr
  obtain ⟨ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂⟩ := h4 htr'
  have e00 : g 0 0 = 1 := Complex.ext (by simpa using ha₁) (by simpa using ha₂)
  have e01 : g 0 1 = 0 := Complex.ext (by simpa using hb₁) (by simpa using hb₂)
  have e10 : g 1 0 = 0 := Complex.ext (by simpa using hc₁) (by simpa using hc₂)
  have e11 : g 1 1 = 1 := Complex.ext (by simpa using hd₁) (by simpa using hd₂)
  refine Matrix.SpecialLinearGroup.ext _ _
    (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩)
  · simp [e00]
  · simp [e01]
  · simp [e10]
  · simp [e11]

end ReusedB

section EisGroup

open MatrixGroups Quaternion

theorem entry_mem_of_mem_eisGroup {g : SL(2, ℂ)} (hg : g ∈ eisGroup) (i j : Fin 2) :
    ∃ z : EisInt, EisInt.toC z = g i j := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, by simp⟩

theorem mem_eisGroup_iff {g : SL(2, ℂ)} :
    g ∈ eisGroup ↔ ∀ i j, ∃ z : EisInt, EisInt.toC z = g i j := by
  refine ⟨entry_mem_of_mem_eisGroup, fun hg => ?_⟩
  choose h hh using hg
  have hdet : (Matrix.of h).det = 1 := by
    apply EisInt.toC_injective
    change EisInt.toComplex _ = EisInt.toComplex 1
    rw [RingHom.map_det, map_one]
    convert g.2 using 2
    ext i j
    simp [hh]
  exact ⟨⟨Matrix.of h, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hh]⟩

/-- Only finitely many Eisenstein integers lie in a disc: `2(a² - ab + b²) ≥ a², b²`. -/
theorem finite_eisInt_normSq_le (M : ℝ) :
    {w : ℂ | (∃ z : EisInt, EisInt.toC z = w) ∧ Complex.normSq w ≤ M}.Finite := by
  have key : ∀ k : ℤ, (k : ℝ) ^ 2 ≤ 2 * M → k ∈ Set.Icc (-⌈1 + 2 * M⌉) ⌈1 + 2 * M⌉ := by
    intro k hk
    have hc := Int.le_ceil (1 + 2 * M)
    have h1 : (k : ℝ) ≤ ⌈1 + 2 * M⌉ := by nlinarith [sq_nonneg ((k : ℝ) - 1), sq_nonneg (k : ℝ)]
    have h2 : (-⌈1 + 2 * M⌉ : ℝ) ≤ k := by nlinarith [sq_nonneg ((k : ℝ) + 1), sq_nonneg (k : ℝ)]
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
  refine (((Set.finite_Icc (-⌈1 + 2 * M⌉) ⌈1 + 2 * M⌉).prod
    (Set.finite_Icc (-⌈1 + 2 * M⌉) ⌈1 + 2 * M⌉)).image
    fun x : ℤ × ℤ => EisInt.toC ⟨x.1, x.2⟩).subset ?_
  rintro w ⟨⟨z, rfl⟩, hw⟩
  rw [EisInt.normSq_toC] at hw
  push_cast at hw
  exact ⟨(z.a, z.b), ⟨key _ (by nlinarith [sq_nonneg ((z.a : ℝ) - z.b), sq_nonneg (z.b : ℝ)]),
    key _ (by nlinarith [sq_nonneg ((z.a : ℝ) - z.b), sq_nonneg (z.a : ℝ)])⟩, rfl⟩

theorem finite_eisGroup_entries_le (M : ℝ) :
    {g : SL(2, ℂ) | g ∈ eisGroup ∧ ∀ i j, Complex.normSq (g i j) ≤ M}.Finite := by
  have hS := Set.Finite.pi (ι := Fin 2) fun _ => Set.Finite.pi (ι := Fin 2) fun _ =>
    finite_eisInt_normSq_le M
  refine (hS.preimage (f := fun (g : SL(2, ℂ)) (i j : Fin 2) => g i j)
    fun g₁ _ g₂ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j =>
      congrFun (congrFun h i) j).subset ?_
  rintro g ⟨hg, hb⟩
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  exact fun i j => ⟨entry_mem_of_mem_eisGroup hg i j, hb i j⟩

/-- A subgroup of `SL(2, ℂ)` with only finitely many elements whose entries lie in any given
disc acts properly discontinuously: the argument of M2.4, with the arithmetic isolated. -/
theorem properlyDiscontinuous_of_finite_entries {Γ : Subgroup SL(2, ℂ)}
    (hfin : ∀ M : ℝ, {g : SL(2, ℂ) | g ∈ Γ ∧ ∀ i j, Complex.normSq (g i j) ≤ M}.Finite)
    (K : Set H3) (hK : IsCompact K) :
    {g : Γ | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite := by
  obtain ⟨t₀, T, R, ht₀, hbox⟩ := exists_box_of_isCompact hK
  refine ((hfin (entryBound t₀ T R)).preimage Subtype.val_injective.injOn).subset ?_
  rintro g ⟨_, ⟨p, hp, rfl⟩, hgp⟩
  exact ⟨g.2, entries_bound (g : SL(2, ℂ)) ht₀ (hbox p hp) (hbox _ hgp)⟩

/-- Every subgroup of the Bianchi group acts properly discontinuously on `ℍ³`. -/
theorem properlyDiscontinuous_of_le_eisGroup {Γ : Subgroup SL(2, ℂ)} (hΓ : Γ ≤ eisGroup)
    (K : Set H3) (hK : IsCompact K) :
    {g : Γ | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite :=
  properlyDiscontinuous_of_finite_entries
    (fun M => (finite_eisGroup_entries_le M).subset fun _ hg => ⟨hΓ hg.1, hg.2⟩) K hK

end EisGroup

section EisCongruence

open MatrixGroups

theorem gammaSeven_le_eisGroup : gammaSeven ≤ eisGroup := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem eisMap_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map EisInt.toComplex :
      SL(2, EisInt) →* SL(2, ℂ)) := fun g₁ g₂ h =>
  Matrix.SpecialLinearGroup.ext _ _ fun i j => EisInt.toC_injective (by
    simpa using congrArg (fun g : SL(2, ℂ) => g i j) h)

/-- The congruence subgroup has finite index in the Bianchi group. -/
theorem relIndex_gammaSeven_eisGroup : gammaSeven.relIndex eisGroup ≠ 0 := by
  rw [gammaSeven, eisGroup, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ eisMap_injective, Subgroup.relIndex_top_right]
  show (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealP)).ker.index ≠ 0
  exact Subgroup.FiniteIndex.index_ne_zero

theorem sub_one_mem_of_mem_gammaSevenZ {h : SL(2, EisInt)} (hh : h ∈ gammaSevenZ)
    (i : Fin 2) : h i i - 1 ∈ idealP := by
  rw [gammaSevenZ, MonoidHom.mem_ker] at hh
  have e := congrArg (fun g : SL(2, EisInt ⧸ idealP) => g i i) hh
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at e
  rw [← map_one (Ideal.Quotient.mk idealP), Ideal.Quotient.eq] at e
  exact e

theorem trace_sub_two_mem_idealP {h : SL(2, EisInt)} (hh : h ∈ gammaSevenZ) :
    h 0 0 + h 1 1 - 2 ∈ idealP := by
  have := add_mem (sub_one_mem_of_mem_gammaSevenZ hh 0) (sub_one_mem_of_mem_gammaSevenZ hh 1)
  convert this using 1
  ring

/-- The only real Eisenstein integer in `[-2, 2]` congruent to `2` modulo `3 + ω` is `2`. -/
theorem eq_two_of_sub_two_mem_idealP {τ : EisInt} (hmem : τ - 2 ∈ idealP) (hb : τ.b = 0)
    (hlo : -2 ≤ τ.a) (hhi : τ.a ≤ 2) : τ = 2 := by
  rw [mem_idealP_iff] at hmem
  change (7 : ℤ) ∣ 2 * (τ.a - ((2 : ℕ) : ℤ)) + (τ.b - 0) at hmem
  apply EisInt.ext
  · change τ.a = ((2 : ℕ) : ℤ); omega
  · change τ.b = 0; exact hb

/-- **Freeness.** No element of the congruence subgroup other than the identity fixes a point. -/
theorem gammaSeven_free {g : SL(2, ℂ)} (hg : g ∈ gammaSeven) (hne : g ≠ 1) (p : H3) :
    g • p ≠ p := by
  intro hfix
  obtain ⟨him, hlo, hhi, hone⟩ := fixed_point_trace g p hfix
  refine hne (hone ?_)
  obtain ⟨h, hh, rfl⟩ := hg
  have htr : (Matrix.SpecialLinearGroup.map EisInt.toComplex h) 0 0 +
      (Matrix.SpecialLinearGroup.map EisInt.toComplex h) 1 1 = EisInt.toC (h 0 0 + h 1 1) := by
    rw [EisInt.toC_add]
    simp
  rw [htr] at him hlo hhi ⊢
  rw [EisInt.toC_im] at him
  rw [EisInt.toC_re] at hlo hhi
  have hb : (h 0 0 + h 1 1).b = 0 := by
    have hs : Real.sqrt 3 / 2 ≠ 0 := by have := sqrt3_pos; positivity
    have h0 : ((h 0 0 + h 1 1).b : ℝ) = 0 := (mul_eq_zero.1 him).resolve_right hs
    exact_mod_cast h0
  rw [hb] at hlo hhi
  have hlo' : (-2 : ℝ) ≤ ((h 0 0 + h 1 1).a : ℝ) := by simpa using hlo
  have hhi' : ((h 0 0 + h 1 1).a : ℝ) ≤ 2 := by simpa using hhi
  rw [eq_two_of_sub_two_mem_idealP (trace_sub_two_mem_idealP hh) hb
    (by exact_mod_cast hlo') (by exact_mod_cast hhi')]
  exact map_ofNat EisInt.toComplex 2

/-- The congruence subgroup of level `3 + ω` is a Kleinian group. -/
theorem isKleinian_gammaSeven : IsKleinian gammaSeven where
  isometry g p q := hdist_smul (g : SL(2, ℂ)) p q
  measure_preserving g := measurePreserving_smul (g : SL(2, ℂ))
  free g hg p := gammaSeven_free g.2 (fun h => hg (Subtype.ext h)) p
  properly_discontinuous := properlyDiscontinuous_of_le_eisGroup gammaSeven_le_eisGroup

end EisCongruence

end Thurston23

open MeasureTheory in
theorem solution : Thurston23.IsKleinian Thurston23.gammaSeven :=
  Thurston23.isKleinian_gammaSeven
