-- Prove2me | solution 1 for Thurston23.isFundamentalDomain_eisBox
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-14T16:24:21.537219+00:00
-- url     : https://prove2.me/submissions/6aa40d7b-d5ee-40c2-965b-930462235e3f

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_eisenstein

/-!
The box over the rhombus is a fundamental domain for the Bianchi group acting effectively.
Verbatim from the mission's source files: helper lemmas of `Thurston23.lean`, and the sections
`EisGroup`, `EisBase`, `EisReduction`, `EisUniqueness`, `EisFundamentalDomain` of
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

/-- The height of `g • p` is the height of `p` divided by `|c q + d|²`. -/
theorem smul_height (g : SL(2, ℂ)) (p : H3) :
    (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
  (mobiusQ_imJ g (toQ_imK p)).1

end ReusedA

section ReusedB

open Set MatrixGroups Quaternion Pointwise

theorem normSq_toQ (p : H3) : normSq (toQ p) = N p.1 := by
  rw [normSq_def']; simp [toQ, N]; ring

/-- The denominator of the Möbius action, split into its complex and vertical parts:
`|c q + d|² = |c z + d|² + |c|² t²`. -/
theorem normSq_denom (c d : ℂ) (p : H3) :
    normSq ((c : ℍ) * toQ p + (d : ℍ))
      = Complex.normSq (c * zc p + d) + Complex.normSq c * (p.1 2) ^ 2 := by
  simp [normSq_def', toQ, zc, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- A triangular element factors as a rotation-dilation followed by a translation,
with no division: `g = T (b a) * D a`. -/
theorem sl2_eq_of_eq_zero' (g : SL(2, ℂ)) (hc : g 1 0 = 0) (ha : g 0 0 ≠ 0) :
    g = T (g 0 1 * g 0 0) * D (g 0 0) ha := by
  have hdet := sl2_det g
  have hd : g 1 1 = (g 0 0)⁻¹ := by
    rw [hc, mul_zero, sub_zero] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [T, D, Matrix.mul_apply, Fin.sum_univ_two, hc, hd] <;>
    field_simp

/-- The coordinates of a rotation-dilation. -/
theorem D_smul_coord (a : ℂ) (ha : a ≠ 0) (p : H3) :
    (D a ha • p).1 0 = (a.re ^ 2 - a.im ^ 2) * p.1 0 - 2 * (a.re * a.im) * p.1 1 ∧
    (D a ha • p).1 1 = 2 * (a.re * a.im) * p.1 0 + (a.re ^ 2 - a.im ^ 2) * p.1 1 ∧
    (D a ha • p).1 2 = (a.re ^ 2 + a.im ^ 2) * p.1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [D_smul_val]
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    try ring
    try tauto
  · rw [D_smul_val]
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    try ring
    try tauto
  · rw [D_smul_val]
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    try ring
    try tauto

/-- An element whose matrix is `± 1` acts trivially: `-1` cancels against its
inverse in the Möbius formula. -/
theorem smul_eq_self_of_coe_eq_pm_one {g : SL(2, ℂ)}
    (h : (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1) (q : H3) :
    g • q = q := by
  rcases h with h | h
  · rw [show g = 1 from Subtype.ext h, one_smul]
  · apply toQ_injective
    rw [toQ_smul]
    have e00 : g 0 0 = -1 := by rw [h]; simp [Matrix.one_apply]
    have e01 : g 0 1 = 0 := by rw [h]; simp [Matrix.one_apply]
    have e10 : g 1 0 = 0 := by rw [h]; simp [Matrix.one_apply]
    have e11 : g 1 1 = -1 := by rw [h]; simp [Matrix.one_apply]
    rw [mobiusQ, e00, e01, e10, e11, coe_neg_one]
    simp

/-- A subset of `H3` lying over a Lebesgue-null set of `ℝ³` has hyperbolic volume zero. -/
theorem hvol_preimage_eq_zero {A : Set (Fin 3 → ℝ)} (hA : MeasurableSet A)
    (h : volume A = 0) : hvol (Subtype.val ⁻¹' A) = 0 := by
  have hs : MeasurableSet (Subtype.val ⁻¹' A : Set H3) := measurable_subtype_coe hA
  rw [hvol_apply hs]
  have hsub : Subtype.val '' (Subtype.val ⁻¹' A : Set H3) ⊆ A := Set.image_preimage_subset _ _
  exact setLIntegral_measure_zero _ _ (measure_mono_null hsub h)

/-- A coordinate hyperplane of `ℝ³` is null. -/
theorem volume_coord_eq (i : Fin 3) (c : ℝ) : volume {x : Fin 3 → ℝ | x i = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) i c

/-- The unit sphere of `ℝ³` is null: transported to `EuclideanSpace`, where spheres
are null for the Haar measure. -/
theorem volume_normOne : volume {x : Fin 3 → ℝ | N x = 1} = 0 := by
  have hset : {x : Fin 3 → ℝ | N x = 1}
      = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹' Metric.sphere 0 1 := by
    ext x
    have hNdef : N x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := rfl
    have hN : 0 ≤ N x := by
      rw [hNdef]
      nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]
    have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (N x) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      rw [hNdef, Fin.sum_univ_three]
      simp [Real.norm_eq_abs, sq_abs, sq]
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_sphere, dist_zero_right, hnorm]
    constructor
    · intro h
      rw [h, Real.sqrt_one]
    · intro h
      have hsq := Real.sq_sqrt hN
      rw [h] at hsq
      simpa using hsq.symm
  rw [hset, (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    (Metric.isClosed_sphere.measurableSet).nullMeasurableSet]
  exact Measure.addHaar_sphere _ _ _

end ReusedB

open MatrixGroups in
instance : SMulInvariantMeasure SL(2, ℂ) H3 hvol :=
  ⟨fun g _ hs => (measurePreserving_smul g).measure_preimage hs.nullMeasurableSet⟩

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

end EisGroup

section EisBase

open Complex

theorem eisBase_of_open {w : ℂ} (h : eisBaseOpen w) : eisBase w :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

/-- `|w - f|² = |w|² + N(f) - 2(a - b) u - b v`. -/
theorem normSq_sub_toC (w : ℂ) (f : EisInt) :
    normSq (w - EisInt.toC f) = normSq w + ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ)
      - 2 * (f.a - f.b) * w.re - f.b * (w.re + Real.sqrt 3 * w.im) := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    EisInt.toC_re, EisInt.toC_im]
  push_cast
  linear_combination ((f.b : ℝ) ^ 2 / 4) * sqrt3_sq

theorem int_mul_pred_nonneg (n : ℤ) : 0 ≤ n * (n - 1) := by
  rcases le_or_gt n 0 with h | h
  · nlinarith
  · nlinarith

/-- The corner values are nonnegative. -/
theorem eis_corner (a b : ℤ) : 0 ≤ a ^ 2 - a * b + b ^ 2 - a ∧ 0 ≤ a ^ 2 - a * b + b ^ 2 - b ∧
    0 ≤ a ^ 2 - a * b + b ^ 2 - (a - b) := by
  have h1 := int_mul_pred_nonneg a
  have h2 := int_mul_pred_nonneg b
  have h3 := int_mul_pred_nonneg (-b)
  have h4 := int_mul_pred_nonneg (a - b)
  have h5 := int_mul_pred_nonneg (b - a)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- A nonzero Eisenstein integer has norm at least `1`: `4N = (2a - b)² + 3b²`. -/
theorem eis_norm_pos {f : EisInt} (hf : f ≠ 0) : 1 ≤ f.a ^ 2 - f.a * f.b + f.b ^ 2 := by
  by_contra h
  push_neg at h
  have hb2 : f.b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * f.a - f.b), sq_nonneg f.b]
  have hb : f.b = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hb2
  have ha2 : f.a ^ 2 = 0 := by rw [hb] at h; nlinarith [sq_nonneg f.a]
  have ha : f.a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ha2
  exact hf (EisInt.ext ha hb)

/-- The difference `|w - f|² - |w|²` as a convex combination of the corner values. -/
theorem normSq_sub_toC_sub (w : ℂ) (f : EisInt) :
    normSq (w - EisInt.toC f) - normSq w =
      (1 - 2 * w.re) * (1 - (w.re + Real.sqrt 3 * w.im)) * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ)
      + 2 * w.re * (1 - (w.re + Real.sqrt 3 * w.im))
          * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - (f.a - f.b) : ℤ) : ℝ)
      + (1 - 2 * w.re) * (w.re + Real.sqrt 3 * w.im)
          * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.b : ℤ) : ℝ)
      + 2 * w.re * (w.re + Real.sqrt 3 * w.im) * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.a : ℤ) : ℝ) := by
  rw [normSq_sub_toC]
  push_cast
  ring

/-- **The rhombus lies in the Voronoi cell of `0`**: `|w| ≤ |w - f|` for every `f ∈ ℤ[ω]`. -/
theorem cell_of_eisBase {w : ℂ} (hw : eisBase w) (f : EisInt) :
    normSq w ≤ normSq (w - EisInt.toC f) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  obtain ⟨c1, c2, c3⟩ := eis_corner f.a f.b
  have c0 : (0 : ℤ) ≤ f.a ^ 2 - f.a * f.b + f.b ^ 2 := by nlinarith [c1, int_mul_pred_nonneg f.a]
  have e := normSq_sub_toC_sub w f
  have k0 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast c0
  have k1 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.a : ℤ) : ℝ) := by exact_mod_cast c1
  have k2 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.b : ℤ) : ℝ) := by exact_mod_cast c2
  have k3 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - (f.a - f.b) : ℤ) : ℝ) := by
    exact_mod_cast c3
  have t0 : 0 ≤ 1 - 2 * w.re := by linarith
  have t1 : 0 ≤ 1 - (w.re + Real.sqrt 3 * w.im) := by linarith
  have := mul_nonneg (mul_nonneg t0 t1) k0
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) t1) k3
  have := mul_nonneg (mul_nonneg t0 h3) k2
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) h3) k1
  linarith

/-- **The open rhombus lies in the open Voronoi cell**: `|w| < |w - f|` for `f ≠ 0`. -/
theorem cell_strict_of_eisBaseOpen {w : ℂ} (hw : eisBaseOpen w) {f : EisInt} (hf : f ≠ 0) :
    normSq w < normSq (w - EisInt.toC f) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  obtain ⟨c1, c2, c3⟩ := eis_corner f.a f.b
  have c0 := eis_norm_pos hf
  have e := normSq_sub_toC_sub w f
  have k0 : (1 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast c0
  have k1 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.a : ℤ) : ℝ) := by exact_mod_cast c1
  have k2 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.b : ℤ) : ℝ) := by exact_mod_cast c2
  have k3 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - (f.a - f.b) : ℤ) : ℝ) := by
    exact_mod_cast c3
  have t0 : 0 < 1 - 2 * w.re := by linarith
  have t1 : 0 < 1 - (w.re + Real.sqrt 3 * w.im) := by linarith
  have := mul_le_mul_of_nonneg_left k0 (mul_pos t0 t1).le
  have := mul_pos t0 t1
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) t1.le) k3
  have := mul_nonneg (mul_nonneg t0.le h3.le) k2
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) h3.le) k1
  nlinarith

/-- A point of the closed cell translated into the open rhombus was not translated. -/
theorem eq_zero_of_cell_of_eisBaseOpen {w : ℂ}
    (hw : ∀ f : EisInt, normSq w ≤ normSq (w - EisInt.toC f)) {e : EisInt}
    (he : eisBaseOpen (w + EisInt.toC e)) : e = 0 := by
  by_contra hne
  have h1 := cell_strict_of_eisBaseOpen he hne
  rw [add_sub_cancel_right] at h1
  have h2 := hw (-e)
  have hneg : EisInt.toC (-e) = -EisInt.toC e := map_neg EisInt.toComplex e
  rw [hneg, sub_neg_eq_add] at h2
  linarith

/-- The Voronoi cell is invariant under multiplication by a unit. -/
theorem cell_mul_unit {w : ℂ} (hw : ∀ f : EisInt, normSq w ≤ normSq (w - EisInt.toC f))
    {U : EisInt} (hU : normSq (EisInt.toC U) = 1) (f : EisInt) :
    normSq (EisInt.toC U * w) ≤ normSq (EisInt.toC U * w - EisInt.toC f) := by
  have hu1 : EisInt.toC U * (starRingEnd ℂ) (EisInt.toC U) = 1 := by
    rw [Complex.mul_conj, hU, Complex.ofReal_one]
  have hm : EisInt.toC (EisInt.conjE U * f) = EisInt.toC (EisInt.conjE U) * EisInt.toC f :=
    map_mul EisInt.toComplex _ _
  have hfac : EisInt.toC U * w - EisInt.toC f
      = EisInt.toC U * (w - EisInt.toC (EisInt.conjE U * f)) := by
    rw [hm, EisInt.toC_conjE]
    linear_combination (EisInt.toC f) * hu1
  rw [hfac, Complex.normSq_mul, Complex.normSq_mul, hU, one_mul, one_mul]
  exact hw _

/-- On the rhombus `|w|² ≤ ⅓`. -/
theorem normSq_le_of_eisBase {w : ℂ} (hw : eisBase w) : normSq w ≤ 1 / 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have hsq : (Real.sqrt 3 * w.im) ^ 2 = 3 * w.im ^ 2 := by rw [mul_pow, sqrt3_sq]
  rw [Complex.normSq_apply]
  nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 / 2 - w.re),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (w.re + Real.sqrt 3 * w.im))
      (by linarith : (0:ℝ) ≤ 1 + (w.re + Real.sqrt 3 * w.im) - 2 * w.re)]

/-- The coordinates of `(c + dω) w`. -/
theorem toC_mul_re (U : EisInt) (w : ℂ) :
    (EisInt.toC U * w).re = (U.a - U.b / 2) * w.re - U.b * (Real.sqrt 3 / 2) * w.im := by
  rw [Complex.mul_re, EisInt.toC_re, EisInt.toC_im]

theorem toC_mul_im (U : EisInt) (w : ℂ) :
    (EisInt.toC U * w).im = (U.a - U.b / 2) * w.im + U.b * (Real.sqrt 3 / 2) * w.re := by
  rw [Complex.mul_im, EisInt.toC_re, EisInt.toC_im]

/-- The rotations by `ω` and `ω²` move the open rhombus off itself. -/
theorem not_eisBaseOpen_rot {w : ℂ} (hw : eisBaseOpen w) {U : EisInt}
    (hU : (U.a = -1 ∧ U.b = -1) ∨ (U.a = 0 ∧ U.b = 1)) :
    ¬ eisBaseOpen (EisInt.toC U * w) := by
  rintro ⟨g1, -, g3, -⟩
  obtain ⟨h1, -, h3, -⟩ := hw
  rw [toC_mul_re] at g1 g3
  rw [toC_mul_im] at g3
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, sqrt3_sq]
  rcases hU with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb] at g1 g3
    push_cast at g1 g3
    nlinarith [hs3]
  · rw [ha, hb] at g1 g3
    push_cast at g1 g3
    nlinarith [hs3]

/-- The units of `ℤ[ω]`: `N(U) = 1` leaves six possibilities. -/
theorem eis_unit_cases {U : EisInt} (hU : U.a ^ 2 - U.a * U.b + U.b ^ 2 = 1) :
    (U.a = 1 ∧ U.b = 0) ∨ (U.a = -1 ∧ U.b = 0) ∨ (U.a = 0 ∧ U.b = 1) ∨ (U.a = 0 ∧ U.b = -1) ∨
      (U.a = 1 ∧ U.b = 1) ∨ (U.a = -1 ∧ U.b = -1) := by
  have hb : U.b ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * U.a - U.b)]
  have hb1 : -1 ≤ U.b ∧ U.b ≤ 1 := by constructor <;> nlinarith
  have ha1 : -1 ≤ U.a ∧ U.a ≤ 1 := by
    have : (2 * U.a - U.b) ^ 2 ≤ 4 := by nlinarith [sq_nonneg U.b]
    constructor <;> nlinarith
  obtain ⟨ha0, ha2⟩ := ha1
  obtain ⟨hb0, hb2⟩ := hb1
  have hA : U.a = -1 ∨ U.a = 0 ∨ U.a = 1 := by omega
  have hB : U.b = -1 ∨ U.b = 0 ∨ U.b = 1 := by omega
  rcases hA with ha | ha | ha <;> rcases hB with hb' | hb' | hb' <;> rw [ha, hb'] at hU <;>
    norm_num at hU <;> simp [ha, hb']

end EisBase

section EisReduction

open Set MatrixGroups Quaternion Pointwise

theorem EisInt.toC_neg_one : EisInt.toC (-1) = -1 := by
  show EisInt.toComplex (-1) = -1
  rw [map_neg, map_one]

theorem T_mem_eisGroup (z : EisInt) : T (EisInt.toC z) ∈ eisGroup :=
  mem_eisGroup_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨1, by simp [T, EisInt.toC_one]⟩, ⟨z, by simp [T]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨0, by simp [T, EisInt.toC_zero]⟩, ⟨1, by simp [T, EisInt.toC_one]⟩⟩⟩)

theorem S_mem_eisGroup : S ∈ eisGroup :=
  mem_eisGroup_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨0, by simp [S, EisInt.toC_zero]⟩, ⟨-1, by simp [S, EisInt.toC_neg_one]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨1, by simp [S, EisInt.toC_one]⟩, ⟨0, by simp [S, EisInt.toC_zero]⟩⟩⟩)

/-- For a unit, the inverse is the conjugate. -/
theorem EisInt.toC_inv_of_normSq {U : EisInt} (hU : Complex.normSq (EisInt.toC U) = 1) :
    (EisInt.toC U)⁻¹ = EisInt.toC (EisInt.conjE U) := by
  rw [Complex.inv_def, hU, inv_one, Complex.ofReal_one, mul_one, EisInt.toC_conjE]

theorem D_mem_eisGroup {U : EisInt} (hU : Complex.normSq (EisInt.toC U) = 1)
    (h : EisInt.toC U ≠ 0) : D (EisInt.toC U) h ∈ eisGroup :=
  mem_eisGroup_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨U, by simp [D]⟩, ⟨0, by simp [D, EisInt.toC_zero]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨0, by simp [D, EisInt.toC_zero]⟩,
        ⟨EisInt.conjE U, by simp [D, EisInt.toC_inv_of_normSq hU]⟩⟩⟩)

theorem zc_T_smul (b : ℂ) (p : H3) : zc (T b • p) = zc p + b := by
  apply Complex.ext <;> simp [zc, T_smul_val]

theorem height_T_smul (b : ℂ) (p : H3) : (T b • p).1 2 = p.1 2 := by
  simp [T_smul_val]

theorem zc_D_smul (a : ℂ) (ha : a ≠ 0) (p : H3) : zc (D a ha • p) = a ^ 2 * zc p := by
  obtain ⟨h0, h1, -⟩ := D_smul_coord a ha p
  apply Complex.ext
  · rw [zc_re, h0]
    simp only [sq, Complex.mul_re, Complex.mul_im, zc_re, zc_im]
    ring
  · rw [zc_im, h1]
    simp only [sq, Complex.mul_re, Complex.mul_im, zc_re, zc_im]
    ring

theorem N_eq_normSq_zc (p : H3) : N p.1 = Complex.normSq (zc p) + p.1 2 * p.1 2 := by
  unfold N
  rw [Complex.normSq_apply, zc_re, zc_im]

theorem N_D_smul_of_normSq (a : ℂ) (ha : a ≠ 0) (hn : Complex.normSq a = 1) (p : H3) :
    N (D a ha • p).1 = N p.1 ∧ (D a ha • p).1 2 = p.1 2 := by
  obtain ⟨-, -, h2⟩ := D_smul_coord a ha p
  have hn' : a.re ^ 2 + a.im ^ 2 = 1 := by rw [Complex.normSq_apply] at hn; linarith
  have ht : (D a ha • p).1 2 = p.1 2 := by rw [h2, hn', one_mul]
  refine ⟨?_, ht⟩
  rw [N_eq_normSq_zc, N_eq_normSq_zc, zc_D_smul, Complex.normSq_mul, map_pow Complex.normSq, hn,
    one_pow, one_mul, ht]

/-- Along an orbit of the Bianchi group only finitely many heights are at least the starting
one. -/
theorem finite_heights_eis (p : H3) :
    ((fun g : SL(2, ℂ) => (g • p).1 2) '' {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2}).Finite := by
  have ht0 : 0 < p.1 2 := p.2
  refine (((finite_eisInt_normSq_le (1 / p.1 2 ^ 2)).prod
    (finite_eisInt_normSq_le (2 * (1 + 1 / p.1 2 ^ 2 * normSq (toQ p))))).image
      fun cd : ℂ × ℂ => p.1 2 / normSq ((cd.1 : ℍ) * toQ p + (cd.2 : ℍ))).subset ?_
  rintro _ ⟨g, ⟨hg, hle⟩, rfl⟩
  have hh := smul_height g p
  have hMpos := normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hc := normSq_mul_imJ_le (g 1 0) (g 1 1) (toQ_imK p)
  rw [show (toQ p).imJ = p.1 2 from rfl] at hc
  generalize hM : ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) = M at hh hMpos hc
  have hM1 : normSq M ≤ 1 := by
    rw [hh, le_div_iff₀ hMpos] at hle
    nlinarith
  have hcb : Complex.normSq (g 1 0) ≤ 1 / p.1 2 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hd : ((g 1 1 : ℂ) : ℍ) = M + -(((g 1 0 : ℂ) : ℍ) * toQ p) := by rw [← hM]; abel
  have hdb := normSq_add_le M (-(((g 1 0 : ℂ) : ℍ) * toQ p))
  rw [← hd, normSq_neg, map_mul, normSq_coeComplex, normSq_coeComplex] at hdb
  have hcq : Complex.normSq (g 1 0) * normSq (toQ p) ≤ 1 / p.1 2 ^ 2 * normSq (toQ p) :=
    mul_le_mul_of_nonneg_right hcb normSq_nonneg
  refine ⟨(g 1 0, g 1 1), ⟨⟨entry_mem_of_mem_eisGroup hg 1 0, hcb⟩,
    ⟨entry_mem_of_mem_eisGroup hg 1 1, by linarith⟩⟩, ?_⟩
  show p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) = (g • p).1 2
  rw [hM, hh]

/-- Every orbit of the Bianchi group has a point of maximal height. -/
theorem exists_max_height_eis (p : H3) :
    ∃ g₀ ∈ eisGroup, ∀ g ∈ eisGroup, (g • p).1 2 ≤ (g₀ • p).1 2 := by
  have h1 : (1 : SL(2, ℂ)) ∈ {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2} :=
    ⟨eisGroup.one_mem, by simp only [one_smul, le_refl]⟩
  have hne : ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2}).Nonempty := ⟨_, 1, h1, rfl⟩
  have hbdd := (finite_heights_eis p).bddAbove
  obtain ⟨g₀, ⟨hg₀, -⟩, hmax⟩ := hne.csSup_mem (finite_heights_eis p)
  have hmax' : (g₀ • p).1 2 = sSup ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2}) := hmax
  refine ⟨g₀, hg₀, fun g hg => ?_⟩
  rw [hmax']
  by_cases hle : p.1 2 ≤ (g • p).1 2
  · exact le_csSup hbdd ⟨g, ⟨hg, hle⟩, rfl⟩
  · exact (not_le.1 hle).le.trans (le_csSup hbdd ⟨1, h1, by simp only [one_smul]⟩)

/-- Every complex number has a nearest point of `ℤ[ω]`, within distance `1`. -/
theorem exists_nearest_eis (z : ℂ) : ∃ e : EisInt, Complex.normSq (z - EisInt.toC e) ≤ 1 ∧
    ∀ f : EisInt, Complex.normSq (z - EisInt.toC e) ≤ Complex.normSq (z - EisInt.toC e - EisInt.toC f) := by
  set Sfin : Set EisInt := {e | Complex.normSq (z - EisInt.toC e) ≤ 1} with hSfin
  have hfin : Sfin.Finite := by
    refine ((finite_eisInt_normSq_le (2 * (Complex.normSq z + 1))).preimage
      EisInt.toC_injective.injOn).subset ?_
    intro e he
    refine ⟨⟨e, rfl⟩, ?_⟩
    have he' : Complex.normSq (z - EisInt.toC e) ≤ 1 := he
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at he' ⊢
    nlinarith [sq_nonneg (2 * z.re - (EisInt.toC e).re), sq_nonneg (2 * z.im - (EisInt.toC e).im)]
  have hne : Sfin.Nonempty := by
    have hs := sqrt3_pos
    set t : ℝ := 2 * z.im / Real.sqrt 3 with ht
    have hzim : z.im = t * Real.sqrt 3 / 2 := by rw [ht]; field_simp
    set rt : ℝ := ((round t : ℤ) : ℝ) with hrt
    set R : ℝ := ((round (z.re + rt / 2) : ℤ) : ℝ) with hR
    refine ⟨⟨round (z.re + rt / 2), round t⟩, ?_⟩
    show Complex.normSq (z - EisInt.toC _) ≤ 1
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, EisInt.toC_re, EisInt.toC_im]
    have h1 := abs_le.1 (abs_sub_round (z.re + rt / 2))
    have h2 := abs_le.1 (abs_sub_round t)
    rw [← hR] at h1
    rw [← hrt] at h2
    simp only
    rw [← hR, ← hrt, hzim]
    have e2 : (t * Real.sqrt 3 / 2 - rt * (Real.sqrt 3 / 2)) * (t * Real.sqrt 3 / 2 - rt * (Real.sqrt 3 / 2))
        = 3 / 4 * (t - rt) ^ 2 := by
      linear_combination ((t - rt) ^ 2 / 4) * sqrt3_sq
    rw [e2]
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨e, he, hmin⟩ := Set.exists_min_image Sfin (fun e => Complex.normSq (z - EisInt.toC e)) hfin hne
  refine ⟨e, he, fun f => ?_⟩
  have hadd : EisInt.toC (e + f) = EisInt.toC e + EisInt.toC f := map_add EisInt.toComplex e f
  by_cases h : Complex.normSq (z - EisInt.toC e - EisInt.toC f) ≤ 1
  · have hmem : e + f ∈ Sfin := by
      show Complex.normSq (z - EisInt.toC (e + f)) ≤ 1
      rw [hadd, ← sub_sub]
      exact h
    have := hmin (e + f) hmem
    simp only at this
    rw [hadd, ← sub_sub] at this
    exact this
  · push_neg at h
    exact le_trans he h.le

/-- The Voronoi cell together with the sector `x ≥ 0`, `x + √3 y ≥ 0` gives the rhombus. -/
theorem eisBase_of_cell {w : ℂ} (hw : ∀ f : EisInt, Complex.normSq w ≤ Complex.normSq (w - EisInt.toC f))
    (h0 : 0 ≤ w.re) (h1 : 0 ≤ w.re + Real.sqrt 3 * w.im) : eisBase w := by
  have c1 := hw ⟨1, 0⟩
  have c2 := hw ⟨1, 1⟩
  rw [normSq_sub_toC] at c1 c2
  push_cast at c1 c2
  exact ⟨h0, by linarith, h1, by linarith⟩

/-- **Reduction.** The Bianchi group carries every point into the box over the rhombus. -/
theorem exists_smul_mem_eisBox (p : H3) : ∃ g ∈ eisGroup, g • p ∈ eisBox := by
  obtain ⟨g₀, hg₀, hmax⟩ := exists_max_height_eis p
  obtain ⟨e, -, hcell⟩ := exists_nearest_eis (zc (g₀ • p))
  have hg₁ : T (EisInt.toC (-e)) * g₀ ∈ eisGroup := eisGroup.mul_mem (T_mem_eisGroup _) hg₀
  set g₁ := T (EisInt.toC (-e)) * g₀ with hg₁def
  have hneg : EisInt.toC (-e) = -EisInt.toC e := map_neg EisInt.toComplex e
  have hz₁ : zc (g₁ • p) = zc (g₀ • p) - EisInt.toC e := by
    rw [hg₁def, mul_smul, zc_T_smul, hneg, ← sub_eq_add_neg]
  have ht₁ : (g₁ • p).1 2 = (g₀ • p).1 2 := by rw [hg₁def, mul_smul, height_T_smul]
  -- `|q| ≥ 1`, since otherwise `S` raises the height
  have hN₁ : 1 ≤ N (g₁ • p).1 := by
    by_contra hlt
    push_neg at hlt
    have hS10 : S 1 0 = 1 := by simp [S]
    have hS11 : S 1 1 = 0 := by simp [S]
    have hht : ((S * g₁) • p).1 2 = (g₁ • p).1 2 / N (g₁ • p).1 := by
      rw [mul_smul, smul_height S (g₁ • p), hS10, hS11, coeComplex_one, coeComplex_zero, one_mul,
        add_zero, normSq_toQ]
    have hNpos : 0 < N (g₁ • p).1 := N_pos (g₁ • p).2
    have hle := hmax _ (eisGroup.mul_mem S_mem_eisGroup hg₁)
    rw [hht, ht₁, div_le_iff₀ hNpos] at hle
    nlinarith [mul_lt_mul_of_pos_left hlt (g₀ • p).2]
  have hcell₁ : ∀ f : EisInt, Complex.normSq (zc (g₁ • p)) ≤ Complex.normSq (zc (g₁ • p) - EisInt.toC f) := by
    rw [hz₁]; exact hcell
  set w := zc (g₁ • p) with hw
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, sqrt3_sq]
  -- rotate into the sector
  by_cases hA : 0 ≤ w.re ∧ 0 ≤ w.re + Real.sqrt 3 * w.im
  · exact ⟨g₁, hg₁, eisBase_of_cell hcell₁ hA.1 hA.2, hN₁⟩
  -- the two rotations, `z ↦ ω z` by `D(ω²)` and `z ↦ ω² z` by `D(ω)`
  have hn1 : Complex.normSq (EisInt.toC ⟨-1, -1⟩) = 1 := by
    rw [EisInt.normSq_toC]; norm_num
  have hn2 : Complex.normSq (EisInt.toC ⟨0, 1⟩) = 1 := by
    rw [EisInt.normSq_toC]; norm_num
  have hne1 : EisInt.toC ⟨-1, -1⟩ ≠ 0 := fun h => by
    rw [h, map_zero] at hn1; exact zero_ne_one hn1
  have hne2 : EisInt.toC ⟨0, 1⟩ ≠ 0 := fun h => by
    rw [h, map_zero] at hn2; exact zero_ne_one hn2
  have hsq1 : EisInt.toC ⟨-1, -1⟩ ^ 2 = EisInt.toC ⟨0, 1⟩ := by
    rw [sq, show EisInt.toC ⟨-1, -1⟩ * EisInt.toC ⟨-1, -1⟩
      = EisInt.toC ((⟨-1, -1⟩ : EisInt) * ⟨-1, -1⟩) from (map_mul EisInt.toComplex _ _).symm]
    exact congrArg EisInt.toC (EisInt.ext (by decide) (by decide))
  have hsq2 : EisInt.toC ⟨0, 1⟩ ^ 2 = EisInt.toC ⟨-1, -1⟩ := by
    rw [sq, show EisInt.toC ⟨0, 1⟩ * EisInt.toC ⟨0, 1⟩
      = EisInt.toC ((⟨0, 1⟩ : EisInt) * ⟨0, 1⟩) from (map_mul EisInt.toComplex _ _).symm]
    exact congrArg EisInt.toC (EisInt.ext (by decide) (by decide))
  by_cases hB : w.re + Real.sqrt 3 * w.im ≤ 0 ∧ 0 ≤ w.re - Real.sqrt 3 * w.im
  · refine ⟨D (EisInt.toC ⟨-1, -1⟩) hne1 * g₁,
      eisGroup.mul_mem (D_mem_eisGroup hn1 hne1) hg₁, ?_, ?_⟩
    · rw [mul_smul, zc_D_smul, hsq1, ← hw]
      refine eisBase_of_cell (cell_mul_unit hcell₁ hn2) ?_ ?_
      · rw [toC_mul_re]; push_cast; nlinarith [hB.1]
      · rw [toC_mul_re, toC_mul_im]; push_cast; nlinarith [hB.2, hs3]
    · rw [mul_smul, (N_D_smul_of_normSq _ hne1 hn1 _).1]; exact hN₁
  · refine ⟨D (EisInt.toC ⟨0, 1⟩) hne2 * g₁,
      eisGroup.mul_mem (D_mem_eisGroup hn2 hne2) hg₁, ?_, ?_⟩
    · rw [mul_smul, zc_D_smul, hsq2, ← hw]
      push_neg at hA hB
      refine eisBase_of_cell (cell_mul_unit hcell₁ hn1) ?_ ?_
      · rw [toC_mul_re]; push_cast
        by_cases hx : 0 ≤ w.re
        · have h1 := hA hx
          have h2 := hB h1.le
          nlinarith
        · push_neg at hx
          by_cases hv : w.re + Real.sqrt 3 * w.im ≤ 0
          · have := hB hv; nlinarith
          · push_neg at hv; nlinarith
      · rw [toC_mul_re, toC_mul_im]; push_cast
        by_cases hx : 0 ≤ w.re
        · have := hA hx
          by_cases hv : w.re + Real.sqrt 3 * w.im ≤ 0
          · have := hB hv; nlinarith [hs3]
          · push_neg at hv; nlinarith [hs3]
        · push_neg at hx; nlinarith [hs3]
    · rw [mul_smul, (N_D_smul_of_normSq _ hne2 hn2 _).1]; exact hN₁

end EisReduction

section EisUniqueness

open Set MatrixGroups Quaternion Pointwise

theorem sq_height_gt_eis {p : H3} (hp : p ∈ eisBoxOpen) : 2 / 3 < p.1 2 ^ 2 := by
  obtain ⟨hb, hN⟩ := hp
  have h1 := normSq_le_of_eisBase (eisBase_of_open hb)
  rw [N_eq_normSq_zc] at hN
  nlinarith

theorem bottomLeft_eq_zero_of_le_one_eis {g : SL(2, ℂ)} (hg : g ∈ eisGroup) {p : H3}
    (hp : p ∈ eisBoxOpen)
    (hD : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ 1) : g 1 0 = 0 := by
  obtain ⟨C, hC⟩ := entry_mem_of_mem_eisGroup hg 1 0
  obtain ⟨Dd, hDd⟩ := entry_mem_of_mem_eisGroup hg 1 1
  rw [normSq_denom] at hD
  have ht2 := sq_height_gt_eis hp
  obtain ⟨hb, hN⟩ := hp
  have hnC : Complex.normSq (g 1 0) = ((C.a ^ 2 - C.a * C.b + C.b ^ 2 : ℤ) : ℝ) := by
    rw [← hC, EisInt.normSq_toC]
  have hn0 : 0 ≤ C.a ^ 2 - C.a * C.b + C.b ^ 2 := by
    nlinarith [sq_nonneg (2 * C.a - C.b), sq_nonneg C.b]
  rw [hnC] at hD
  have hz0 := Complex.normSq_nonneg (g 1 0 * zc p + g 1 1)
  have hnle : C.a ^ 2 - C.a * C.b + C.b ^ 2 ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h2 : (2 : ℝ) ≤ ((C.a ^ 2 - C.a * C.b + C.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast hlt
    nlinarith
  by_cases hC0 : C = 0
  · rw [← hC, hC0]
    exact map_zero EisInt.toComplex
  exfalso
  have hn1 : C.a ^ 2 - C.a * C.b + C.b ^ 2 = 1 := le_antisymm hnle (eis_norm_pos hC0)
  have hc1 : Complex.normSq (g 1 0) = 1 := by rw [hnC, hn1]; norm_num
  have hu1 : g 1 0 * (starRingEnd ℂ) (g 1 0) = 1 := by
    rw [Complex.mul_conj, hc1, Complex.ofReal_one]
  have hm : EisInt.toC (-(EisInt.conjE C * Dd)) = -((starRingEnd ℂ) (g 1 0) * g 1 1) := by
    rw [show EisInt.toC (-(EisInt.conjE C * Dd)) = -(EisInt.toC (EisInt.conjE C) * EisInt.toC Dd)
      from by
        rw [show EisInt.toC (-(EisInt.conjE C * Dd)) = EisInt.toComplex (-(EisInt.conjE C * Dd))
          from rfl, map_neg, map_mul]
        rfl,
      EisInt.toC_conjE, hC, hDd]
  have hfac : g 1 0 * zc p + g 1 1
      = g 1 0 * (zc p - EisInt.toC (-(EisInt.conjE C * Dd))) := by
    rw [hm]
    linear_combination (-(g 1 1)) * hu1
  have hcell := cell_of_eisBase (eisBase_of_open hb) (-(EisInt.conjE C * Dd))
  rw [hfac, Complex.normSq_mul, hc1, one_mul] at hD
  rw [N_eq_normSq_zc] at hN
  have : ((C.a ^ 2 - C.a * C.b + C.b ^ 2 : ℤ) : ℝ) = 1 := by rw [hn1]; norm_num
  rw [this, one_mul] at hD
  nlinarith

/-- **Uniqueness, the triangular case.** -/
theorem smul_eq_self_of_le_one_eis {g : SL(2, ℂ)} (hg : g ∈ eisGroup) {p : H3}
    (hp : p ∈ eisBoxOpen) (hgp : g • p ∈ eisBoxOpen)
    (hD : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ 1) :
    ∀ q : H3, g • q = q := by
  have hc : g 1 0 = 0 := bottomLeft_eq_zero_of_le_one_eis hg hp hD
  obtain ⟨A, hA⟩ := entry_mem_of_mem_eisGroup hg 0 0
  obtain ⟨B, hB⟩ := entry_mem_of_mem_eisGroup hg 0 1
  obtain ⟨Dg, hDg⟩ := entry_mem_of_mem_eisGroup hg 1 1
  have hdet := sl2_det g
  rw [hc, mul_zero, sub_zero] at hdet
  have ha0 : g 0 0 ≠ 0 := fun h => by rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have hd0 : g 1 1 ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  have hDval : Complex.normSq (g 1 1) ≤ 1 := by
    have h := hD
    rw [normSq_denom, hc] at h
    simpa using h
  have hDint : Complex.normSq (g 1 1) = ((Dg.a ^ 2 - Dg.a * Dg.b + Dg.b ^ 2 : ℤ) : ℝ) := by
    rw [← hDg, EisInt.normSq_toC]
  have hDg0 : Dg ≠ 0 := fun h => hd0 (by rw [← hDg, h]; exact map_zero EisInt.toComplex)
  have hDge := eis_norm_pos hDg0
  have hDone : Complex.normSq (g 1 1) = 1 := by
    have : (1 : ℝ) ≤ ((Dg.a ^ 2 - Dg.a * Dg.b + Dg.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast hDge
    rw [hDint] at hDval ⊢
    linarith
  have hnormA : Complex.normSq (g 0 0) = 1 := by
    have hprod : Complex.normSq (g 0 0) * Complex.normSq (g 1 1) = 1 := by
      rw [← Complex.normSq_mul, hdet, Complex.normSq_one]
    rwa [hDone, mul_one] at hprod
  have hAint : A.a ^ 2 - A.a * A.b + A.b ^ 2 = 1 := by
    have h : ((A.a ^ 2 - A.a * A.b + A.b ^ 2 : ℤ) : ℝ) = 1 := by
      rw [← EisInt.normSq_toC, hA, hnormA]
    exact_mod_cast h
  -- `g = T (b a) * D a` acts by `z ↦ a² z + b a`
  have hfac : g = T (g 0 1 * g 0 0) * D (g 0 0) ha0 := sl2_eq_of_eq_zero' g hc ha0
  have hsmul : zc (g • p) = g 0 0 ^ 2 * zc p + g 0 1 * g 0 0 := by
    have : g • p = T (g 0 1 * g 0 0) • (D (g 0 0) ha0 • p) := by
      conv_lhs => rw [hfac]
      rw [mul_smul]
    rw [this, zc_T_smul, zc_D_smul]
  have hU : g 0 0 ^ 2 = EisInt.toC (A * A) := by
    rw [sq, ← hA]
    exact (map_mul EisInt.toComplex A A).symm
  have hE : g 0 1 * g 0 0 = EisInt.toC (B * A) := by
    rw [← hA, ← hB]
    exact (map_mul EisInt.toComplex B A).symm
  have hnU : Complex.normSq (EisInt.toC (A * A)) = 1 := by
    rw [← hU, map_pow Complex.normSq, hnormA, one_pow]
  have hcellw := cell_mul_unit (cell_of_eisBase (eisBase_of_open hp.1)) hnU
  have hgp' : eisBaseOpen (EisInt.toC (A * A) * zc p + EisInt.toC (B * A)) := by
    have := hgp.1
    rwa [hsmul, hU, hE] at this
  have hBA : B * A = 0 := eq_zero_of_cell_of_eisBaseOpen hcellw hgp'
  have hBA0 : EisInt.toC (B * A) = 0 := by rw [hBA]; exact map_zero EisInt.toComplex
  have hb0 : g 0 1 = 0 := by
    have h0 : g 0 1 * g 0 0 = 0 := by rw [hE, hBA0]
    exact (mul_eq_zero.1 h0).resolve_right ha0
  have hrot : eisBaseOpen (EisInt.toC (A * A) * zc p) := by
    rw [hBA0, add_zero] at hgp'
    exact hgp'
  have hAAa : (A * A).a = A.a * A.a - A.b * A.b := rfl
  have hAAb : (A * A).b = A.a * A.b + A.b * A.a - A.b * A.b := rfl
  have h00 : g 0 0 = 1 ∨ g 0 0 = -1 := by
    rcases eis_unit_cases hAint with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
        ⟨ha, hb⟩
    · left
      rw [← hA, show A = 1 from EisInt.ext ha hb]
      exact EisInt.toC_one
    · right
      rw [← hA, show A = -1 from EisInt.ext ha hb]
      exact EisInt.toC_neg_one
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inl ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inl ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inr ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inr ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
  have hdinv : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hmat : (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rcases h00 with h | h
    · refine Or.inl ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h, hb0, hc, hdinv]
    · refine Or.inr ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h, hb0, hc, hdinv]
  exact smul_eq_self_of_coe_eq_pm_one hmat

/-- **Uniqueness for the Bianchi group.** An element carrying a point of the open box to a
point of the open box acts trivially. -/
theorem smul_eq_self_of_mem_eisBoxOpen {g : SL(2, ℂ)} (hg : g ∈ eisGroup) {p : H3}
    (hp : p ∈ eisBoxOpen) (hgp : g • p ∈ eisBoxOpen) : ∀ q : H3, g • q = q := by
  rcases le_or_gt (normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ))) 1 with hD | hD
  · exact smul_eq_self_of_le_one_eis hg hp hgp hD
  have hginv : g⁻¹ ∈ eisGroup := eisGroup.inv_mem hg
  have hpos : 0 < normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
    normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hpos' : 0 < normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) :=
    normSq_pos (denom_ne_zero (sl2_row_ne_zero g⁻¹) (toQ_imK (g • p)) (g • p).2)
  have h1 : (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
    smul_height g p
  have h2 : (g⁻¹ • (g • p)).1 2 = (g • p).1 2 /
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) := smul_height g⁻¹ (g • p)
  rw [inv_smul_smul, h1, div_div] at h2
  have hne : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) ≠ 0 :=
    ne_of_gt (mul_pos hpos hpos')
  have h3 := (eq_div_iff hne).1 h2
  have hmul : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) = 1 := by
    have h4 : p.1 2 * (normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
        normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ))) = p.1 2 * 1 := by
      rw [h3, mul_one]
    exact mul_left_cancel₀ (ne_of_gt p.2) h4
  have hDinv : normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) ≤ 1 := by
    nlinarith [hmul, hD, hpos, hpos']
  have key : ∀ q : H3, g⁻¹ • q = q :=
    smul_eq_self_of_le_one_eis hginv hgp (by rw [inv_smul_smul]; exact hp) hDinv
  intro q
  have h := key (g • q)
  rw [inv_smul_smul] at h
  exact h.symm

end EisUniqueness

section EisFundamentalDomain

open Set MatrixGroups Quaternion Pointwise

/-- The plane `x + √3 y = c` of `ℝ³` is null: it is the preimage of a coordinate plane under a
shear of determinant `1`. -/
theorem volume_plane_sqrt3 (c : ℝ) :
    volume {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c} = 0 := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := !![1, Real.sqrt 3, 0; 0, 1, 0; 0, 0, 1] with hM
  have hdet : LinearMap.det (Matrix.toLin' M) ≠ 0 := by
    rw [LinearMap.det_toLin', Matrix.det_fin_three]
    simp [hM]
  have hset : {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c}
      = (Matrix.toLin' M) ⁻¹' {y : Fin 3 → ℝ | y 0 = c} := by
    ext x
    simp [hM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hset, Measure.addHaar_preimage_linearMap (μ := volume) hdet, volume_coord_eq, mul_zero]

theorem measurableSet_eisBox : MeasurableSet eisBox := by
  have h0 : Measurable fun p : H3 => p.1 0 := (measurable_pi_apply 0).comp measurable_subtype_coe
  have h1 : Measurable fun p : H3 => p.1 1 := (measurable_pi_apply 1).comp measurable_subtype_coe
  have h2 : Measurable fun p : H3 => p.1 2 := (measurable_pi_apply 2).comp measurable_subtype_coe
  have hv : Measurable fun p : H3 => p.1 0 + Real.sqrt 3 * p.1 1 := h0.add (h1.const_mul _)
  have hN : Measurable fun p : H3 => N p.1 := by
    unfold N
    exact ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have hset : eisBox = {p : H3 | 0 ≤ p.1 0} ∩ {p : H3 | p.1 0 ≤ 1 / 2} ∩
      {p : H3 | 0 ≤ p.1 0 + Real.sqrt 3 * p.1 1} ∩ {p : H3 | p.1 0 + Real.sqrt 3 * p.1 1 ≤ 1} ∩
      {p : H3 | 1 ≤ N p.1} := by
    ext p
    simp only [eisBox, eisBase, zc_re, zc_im, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset]
  exact ((((measurableSet_le measurable_const h0).inter (measurableSet_le h0 measurable_const)).inter
    (measurableSet_le measurable_const hv)).inter (measurableSet_le hv measurable_const)).inter
    (measurableSet_le measurable_const hN)

/-- **The boundary of the box is null.** It lies in two coordinate planes, two planes
`x + √3 y = c`, and the unit sphere. -/
theorem hvol_eisBox_sdiff_eisBoxOpen : hvol (eisBox \ eisBoxOpen) = 0 := by
  have hsub : eisBox \ eisBoxOpen ⊆
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 = 0}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 = 1 / 2}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = 0}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = 1}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | N x = 1}) := by
    rintro p ⟨⟨⟨h1, h2, h3, h4⟩, hN⟩, hopen⟩
    have hopen' : ¬ (eisBaseOpen (zc p) ∧ 1 < N p.1) := hopen
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · rcases h3.lt_or_eq with h3 | h3
        · rcases h4.lt_or_eq with h4 | h4
          · exact Or.inr (le_antisymm (not_lt.1 fun hlt => hopen' ⟨⟨h1, h2, h3, h4⟩, hlt⟩) hN)
          · exact Or.inl (Or.inr h4)
        · exact Or.inl (Or.inl (Or.inr h3.symm))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1.symm)))
  refine measure_mono_null hsub ?_
  have hplane : ∀ (i : Fin 3) (c : ℝ),
      hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x i = c}) = 0 := by
    intro i c
    refine hvol_preimage_eq_zero ?_ (volume_coord_eq i c)
    have hset : {x : Fin 3 → ℝ | x i = c} = (fun f : Fin 3 → ℝ => f i) ⁻¹' {c} := rfl
    rw [hset]
    exact measurable_pi_apply i (measurableSet_singleton c)
  have hplane3 : ∀ c : ℝ,
      hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c}) = 0 := by
    intro c
    refine hvol_preimage_eq_zero ?_ (volume_plane_sqrt3 c)
    have hset : {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c}
        = (fun f : Fin 3 → ℝ => f 0 + Real.sqrt 3 * f 1) ⁻¹' {c} := rfl
    rw [hset]
    exact ((measurable_pi_apply 0).add ((measurable_pi_apply 1).const_mul _))
      (measurableSet_singleton c)
  have hsphere : hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | N x = 1}) = 0 := by
    refine hvol_preimage_eq_zero ?_ volume_normOne
    have : {x : Fin 3 → ℝ | N x = 1}
        = (fun x : Fin 3 → ℝ => x 0 * x 0 + x 1 * x 1 + x 2 * x 2) ⁻¹' {1} := rfl
    rw [this]
    exact ((((measurable_pi_apply 0).mul (measurable_pi_apply 0)).add
      ((measurable_pi_apply 1).mul (measurable_pi_apply 1))).add
      ((measurable_pi_apply 2).mul (measurable_pi_apply 2))) (measurableSet_singleton 1)
  exact measure_union_null (measure_union_null (measure_union_null (measure_union_null
    (hplane 0 0) (hplane 0 (1 / 2))) (hplane3 0)) (hplane3 1)) hsphere

/-- **The fundamental domain.** The closed box over the rhombus is a fundamental domain for the Bianchi group acting
effectively. Covering is `exists_smul_mem_eisBox`; disjointness is uniqueness on
the open box, since the boundary is null. -/
theorem isFundamentalDomain_eisBox : IsFundamentalDomain EisEff eisBox hvol := by
  refine IsFundamentalDomain.mk'' measurableSet_eisBox.nullMeasurableSet ?_ ?_ ?_
  · filter_upwards with p
    obtain ⟨g, hg, hgp⟩ := exists_smul_mem_eisBox p
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, hgp⟩
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hsub : ((QuotientGroup.mk g : EisEff) • eisBox) ∩ eisBox ⊆
          ((g : SL(2, ℂ)) • (eisBox \ eisBoxOpen)) ∪ (eisBox \ eisBoxOpen) := by
        rintro p ⟨hp1, hp2⟩
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨hcon1, hcon2⟩ := hcon
        have hopen : p ∈ eisBoxOpen := by
          by_contra h
          exact hcon2 ⟨hp2, h⟩
        have hinv : (g : SL(2, ℂ))⁻¹ • p ∈ eisBox := by
          rw [EisEff.mk_smul_set, Set.mem_smul_set_iff_inv_smul_mem] at hp1
          exact hp1
        have hinvopen : (g : SL(2, ℂ))⁻¹ • p ∈ eisBoxOpen := by
          by_contra h
          refine hcon1 ?_
          rw [Set.mem_smul_set_iff_inv_smul_mem]
          exact ⟨hinv, h⟩
        have htriv : ∀ r : H3, (g : SL(2, ℂ))⁻¹ • r = r :=
          smul_eq_self_of_mem_eisBoxOpen (eisGroup.inv_mem g.2) hopen hinvopen
        have htrivg : ∀ r : H3, (g : SL(2, ℂ)) • r = r := by
          intro r
          have h := htriv ((g : SL(2, ℂ)) • r)
          rw [inv_smul_smul] at h
          exact h.symm
        refine hq ?_
        refine (QuotientGroup.eq_one_iff _).2 ?_
        rw [eisKer, MonoidHom.mem_ker]
        refine Equiv.ext fun r => ?_
        exact htrivg r
      refine measure_mono_null hsub ?_
      refine measure_union_null ?_ hvol_eisBox_sdiff_eisBoxOpen
      rw [measure_smul]
      exact hvol_eisBox_sdiff_eisBoxOpen
  · intro q
    exact (EisEff.measurePreserving q).quasiMeasurePreserving

end EisFundamentalDomain

end Thurston23

open MeasureTheory in
theorem solution :
    MeasureTheory.IsFundamentalDomain Thurston23.EisEff Thurston23.eisBox Thurston23.hvol :=
  Thurston23.isFundamentalDomain_eisBox
