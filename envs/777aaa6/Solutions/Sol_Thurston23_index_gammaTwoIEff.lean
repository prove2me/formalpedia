-- Prove2me | solution 1 for Thurston23.index_gammaTwoIEff
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T16:29:43.425314+00:00
-- url     : https://prove2.me/submissions/65a56e73-ccad-4895-9d07-0906dd2a606d

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_picard

/-!
The index of `Γ(2 + i)` in the effective Picard group is `60`: reduction modulo `2 + i` maps
`SL(2, ℤ[i])` onto `SL(2, 𝔽₅)`, of order `120` (lifting through `SL(2, ℤ)`, and `decide`), and the
kernel of the Picard action is `{±1}` with `-1 ∉ Γ(2 + i)`. Verbatim from the mission's source
file `Thurston23.lean`, sections `IndexOfGamma`, `KernelPmOne`, `IndexSixty`, with the few
lemmas they use from the sections `Picard` and `Congruence`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

open Set MatrixGroups Quaternion Pointwise

theorem entry_mem_of_mem_picard {g : SL(2, ℂ)} (hg : g ∈ picard) (i j : Fin 2) :
    ∃ z : GaussianInt, (z : ℂ) = g i j := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, by simp⟩

theorem mem_picard_iff {g : SL(2, ℂ)} :
    g ∈ picard ↔ ∀ i j, ∃ z : GaussianInt, (z : ℂ) = g i j := by
  refine ⟨entry_mem_of_mem_picard, fun hg => ?_⟩
  choose h hh using hg
  have hdet : (Matrix.of h).det = 1 := by
    apply GaussianInt.toComplex_injective
    rw [RingHom.map_det, map_one]
    convert g.2 using 2
    ext i j
    simp [hh]
  exact ⟨⟨Matrix.of h, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hh]⟩


theorem smul_height (g : SL(2, ℂ)) (p : H3) :
    (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
  (mobiusQ_imJ g (toQ_imK p)).1

/-- If `g` moves a point of the box to a point of the box, then `|c q + d|² ≤ T / t₀`, so
`|c|² ≤ T / t₀³` and `|d|² ≤ 2 (T / t₀ + R T / t₀³)`. -/


theorem sl2Map_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map GaussianInt.toComplex :
      SL(2, GaussianInt) →* SL(2, ℂ)) := fun g₁ g₂ h =>
  Matrix.SpecialLinearGroup.ext _ _ fun i j => GaussianInt.toComplex_injective (by
    simpa using congrArg (fun g : SL(2, ℂ) => g i j) h)

/-- **M2.5, finite index.** `Γ(2 + i)` has finite index in the Picard group. -/

theorem sub_one_mem_of_mem_gammaTwoIZ {h : SL(2, GaussianInt)} (hh : h ∈ gammaTwoIZ)
    (i : Fin 2) : h i i - 1 ∈ idealTwoI := by
  rw [gammaTwoIZ, MonoidHom.mem_ker] at hh
  have e := congrArg (fun g : SL(2, GaussianInt ⧸ idealTwoI) => g i i) hh
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at e
  rw [← map_one (Ideal.Quotient.mk idealTwoI), Ideal.Quotient.eq] at e
  exact e


/-! ## The index of `Γ(2 + i)`: reduction modulo `2 + i` is onto `SL(2, 𝔽₅)`

`[SL(2, ℤ[i]) : Γ(2+i)] = |SL(2, 𝔽₅)| = 120`. Mathlib has no surjectivity of
`SL(2, R) → SL(2, R/I)`, so it is proved here for `ℤ[i] → ℤ[i]/(2+i) ≅ 𝔽₅` by lifting
through `SL(2, ℤ)`: a first row with coprime integer lifts (a Chinese-remainder choice), Bézout
coefficients for the second row, and a lower unipotent correction whose residue `decide` finds.
The order of `SL(2, 𝔽₅)` is counted by `decide` on the quadruples with `ad - bc = 1`. -/

section IndexOfGamma

open Set MatrixGroups

section ReductionSurjective

/-- Integers in `(2 + i)` are exactly the multiples of `5`. -/
theorem intCast_mem_idealTwoI_iff (n : ℤ) : (n : GaussianInt) ∈ idealTwoI ↔ (5 : ℤ) ∣ n := by
  rw [idealTwoI, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, hw⟩
    have hre := congrArg Zsqrtd.re hw
    have hi := congrArg Zsqrtd.im hw
    simp at hre hi
    exact ⟨-w.im, by omega⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨2 * k, -k⟩, ?_⟩
    ext <;> simp
    ring

theorem mk_intCast_eq_of_dvd {m n : ℤ} (h : (5 : ℤ) ∣ m - n) :
    Ideal.Quotient.mk idealTwoI (m : GaussianInt) = Ideal.Quotient.mk idealTwoI (n : GaussianInt) := by
  rw [Ideal.Quotient.eq, ← Int.cast_sub, intCast_mem_idealTwoI_iff]
  exact h

/-- Every class modulo `2 + i` is the class of an integer. -/
theorem exists_int_rep (x : GaussianInt ⧸ idealTwoI) :
    ∃ n : ℤ, Ideal.Quotient.mk idealTwoI (n : GaussianInt) = x := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨z.re - 2 * z.im, ?_⟩
  rw [Ideal.Quotient.eq, idealTwoI, Ideal.mem_span_singleton]
  refine ⟨⟨-z.im, 0⟩, ?_⟩
  ext <;> simp

set_option maxRecDepth 10000 in
/-- The adjustment of the lower row, checked on all residues: given a first row `(a, b)` with
`a d - b c = 1` and Bézout coefficients `u a + v b = 1`, some `t` makes `(t a - v, t b + u)`
equal to `(c, d)`. -/
theorem exists_t_zmod : ∀ a b c d u v : ZMod 5, a * d - b * c = 1 → u * a + v * b = 1 →
    ∃ t : ZMod 5, t * a - v = c ∧ t * b + u = d := by decide

theorem isCoprime_five_of_not_dvd {a : ℤ} (ha : ¬ (5 : ℤ) ∣ a) : IsCoprime (5 : ℤ) a := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have h : Nat.Coprime 5 a.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 fun h5 => ha (Int.ofNat_dvd_left.2 h5)
  exact h

/-- **Lifting to `SL(2, ℤ)`.** A matrix over `ℤ` with determinant `≡ 1 (mod 5)` is congruent
modulo `5` to an element of `SL(2, ℤ)`. -/
theorem exists_sl2Z_lift (a b c d : ℤ) (h : (5 : ℤ) ∣ a * d - b * c - 1) :
    ∃ N : SL(2, ℤ), (5 : ℤ) ∣ N 0 0 - a ∧ (5 : ℤ) ∣ N 0 1 - b ∧
      (5 : ℤ) ∣ N 1 0 - c ∧ (5 : ℤ) ∣ N 1 1 - d := by
  -- a coprime lift of the first row
  obtain ⟨a', b', ha', hb', hcop⟩ : ∃ a' b' : ℤ, (5 : ℤ) ∣ a' - a ∧ (5 : ℤ) ∣ b' - b ∧
      IsCoprime a' b' := by
    by_cases hb : (5 : ℤ) ∣ b
    · have ha : ¬ (5 : ℤ) ∣ a := by
        intro ha
        have h1 : (5 : ℤ) ∣ a * d - b * c :=
          dvd_sub (dvd_mul_of_dvd_left ha d) (dvd_mul_of_dvd_left hb c)
        have h2 : (5 : ℤ) ∣ 1 := by
          have := dvd_sub h1 h
          simp at this
        norm_num at h2
      exact ⟨a, 5, by simp, dvd_sub (dvd_refl 5) hb, (isCoprime_five_of_not_dvd ha).symm⟩
    · obtain ⟨u, v, huv⟩ := isCoprime_five_of_not_dvd hb
      refine ⟨a + 5 * u * (1 - a), b, ⟨u * (1 - a), by ring⟩, by simp, ?_⟩
      have e : a + 5 * u * (1 - a) = 1 + b * (v * (a - 1)) := by
        linear_combination (1 - a) * huv
      rw [e]
      exact isCoprime_one_left.add_mul_left_left _
  obtain ⟨u, v, huv⟩ := hcop
  -- the residues, in `ZMod 5`
  have cast_dvd : ∀ {m n : ℤ}, (5 : ℤ) ∣ m - n → ((m : ZMod 5) = n) := by
    intro m n hmn
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (m - n) 5).2 (by exact_mod_cast hmn)
    push_cast at this
    exact sub_eq_zero.1 this
  have ea : (a' : ZMod 5) = a := cast_dvd ha'
  have eb : (b' : ZMod 5) = b := cast_dvd hb'
  have hdet : (a : ZMod 5) * d - b * c = 1 := by
    have := cast_dvd (n := 1) (by simpa using h)
    push_cast at this
    exact this
  have hbez : (u : ZMod 5) * a + v * b = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 5) huv
    push_cast at this
    rwa [ea, eb] at this
  obtain ⟨t', ht1, ht2⟩ := exists_t_zmod a b c d u v hdet hbez
  set t : ℤ := (t'.val : ℤ) with ht
  have et : (t : ZMod 5) = t' := by
    rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨⟨!![a', b'; t * a' - v, t * b' + u], ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination huv
  · simpa using ha'
  · simpa using hb'
  · show (5 : ℤ) ∣ (t * a' - v) - c
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (t * a' - v - c) 5).1
      (by push_cast; rw [et, ea, ht1, sub_self])
  · show (5 : ℤ) ∣ (t * b' + u) - d
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (t * b' + u - d) 5).1
      (by push_cast; rw [et, eb, ht2, sub_self])

/-- **Reduction modulo `2 + i` is onto.** -/
theorem reduction_surjective :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealTwoI) :
      SL(2, GaussianInt) →* SL(2, GaussianInt ⧸ idealTwoI)) := by
  intro M
  obtain ⟨a, ha⟩ := exists_int_rep (M 0 0)
  obtain ⟨b, hb⟩ := exists_int_rep (M 0 1)
  obtain ⟨c, hc⟩ := exists_int_rep (M 1 0)
  obtain ⟨d, hd⟩ := exists_int_rep (M 1 1)
  have hdet : (5 : ℤ) ∣ a * d - b * c - 1 := by
    rw [← intCast_mem_idealTwoI_iff]
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := M.2
      rwa [Matrix.det_fin_two] at this
    push_cast
    simp only [map_sub, map_mul, map_one]
    rw [ha, hb, hc, hd, hM]
    exact sub_self _
  obtain ⟨N, h00, h01, h10, h11⟩ := exists_sl2Z_lift a b c d hdet
  refine ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom GaussianInt) N, ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    eq_intCast]
  fin_cases i <;> fin_cases j
  · exact (mk_intCast_eq_of_dvd h00).trans ha
  · exact (mk_intCast_eq_of_dvd h01).trans hb
  · exact (mk_intCast_eq_of_dvd h10).trans hc
  · exact (mk_intCast_eq_of_dvd h11).trans hd

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem idealTwoI_ne_top : idealTwoI ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  have := (intCast_mem_idealTwoI_iff 1).not.2 (by norm_num)
  simpa using this

/-- `ℤ[i]/(2 + i)` has characteristic `5`. -/
instance charP_quotTwoI : CharP (GaussianInt ⧸ idealTwoI) 5 where
  cast_eq_zero_iff x := by
    have h1 : ((x : ℕ) : GaussianInt ⧸ idealTwoI)
        = Ideal.Quotient.mk idealTwoI ((x : ℤ) : GaussianInt) := by
      rw [Int.cast_natCast, map_natCast]
    have h2 : ((5 : ℕ) : ℤ) ∣ (x : ℤ) ↔ 5 ∣ x := Int.natCast_dvd_natCast
    have h3 : ((5 : ℕ) : ℤ) = (5 : ℤ) := by norm_num
    rw [h3] at h2
    rw [h1]
    exact (Ideal.Quotient.eq_zero_iff_mem.trans (intCast_mem_idealTwoI_iff x)).trans h2

/-- `ℤ[i]/(2 + i) ≅ 𝔽₅`. -/
noncomputable def zmodFiveEquiv : ZMod 5 ≃+* GaussianInt ⧸ idealTwoI := by
  haveI : Nontrivial (GaussianInt ⧸ idealTwoI) := Ideal.Quotient.nontrivial_iff.2 idealTwoI_ne_top
  refine RingEquiv.ofBijective (ZMod.castHom (dvd_refl 5) (GaussianInt ⧸ idealTwoI))
    ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_rep x
  refine ⟨n, ?_⟩
  rw [ZMod.castHom_apply, ZMod.cast_intCast (dvd_refl 5), ← hn]
  exact (map_intCast (Ideal.Quotient.mk idealTwoI) n).symm

/-- `SL(2, 𝔽₅)` as the quadruples with `a d - b c = 1`. -/
def sl2Quad : SL(2, ZMod 5) ≃
    {x : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1} where
  toFun M := ⟨(M 0 0, M 0 1, M 1 0, M 1 1), by
    have := M.2
    rwa [Matrix.det_fin_two] at this⟩
  invFun x := ⟨!![x.1.1, x.1.2.1; x.1.2.2.1, x.1.2.2.2], by
    rw [Matrix.det_fin_two_of]; exact x.2⟩
  left_inv M := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> rfl
  right_inv x := by
    ext <;> rfl

set_option maxRecDepth 10000 in
theorem card_quad : Fintype.card
    {x : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1} = 120 := by
  decide

theorem card_sl2_zmod_five : Nat.card SL(2, ZMod 5) = 120 := by
  rw [Nat.card_congr sl2Quad, Nat.card_eq_fintype_card, card_quad]

/-- `SL(2, ℤ[i]/(2+i)) ≃ SL(2, 𝔽₅)`. -/
noncomputable def sl2QuotEquiv : SL(2, GaussianInt ⧸ idealTwoI) ≃ SL(2, ZMod 5) where
  toFun := Matrix.SpecialLinearGroup.map zmodFiveEquiv.symm.toRingHom
  invFun := Matrix.SpecialLinearGroup.map zmodFiveEquiv.toRingHom
  left_inv M := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv M := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem card_sl2_quot : Nat.card SL(2, GaussianInt ⧸ idealTwoI) = 120 := by
  rw [Nat.card_congr sl2QuotEquiv, card_sl2_zmod_five]

/-- **`[SL(2, ℤ[i]) : Γ(2+i)] = 120`.** -/
theorem index_gammaTwoIZ : gammaTwoIZ.index = 120 := by
  rw [gammaTwoIZ, Subgroup.index_ker, MonoidHom.range_eq_top.2 reduction_surjective,
    Subgroup.card_top, card_sl2_quot]
end ReductionSurjective

end IndexOfGamma

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

/-! ### The index of `Γ(2 + i)` in the effective Picard group is `60`

The kernel of the action is `{±1}` (an element fixing `(0,0,1)`, `(0,0,2)` and `(1,0,1)` is
`±1`), and `-1 ∉ Γ(2 + i)` since `-1 ≢ 1 (mod 2 + i)`; so the index `120` halves. -/

section KernelPmOne

/-- The point `(x, y, t)` of the half-space. -/
def pt (x y t : ℝ) (ht : 0 < t) : H3 := ⟨![x, y, t], by simpa using ht⟩

theorem toQ_pt_re (x y t : ℝ) (ht : 0 < t) : (toQ (pt x y t ht)).re = x := rfl
theorem toQ_pt_imI (x y t : ℝ) (ht : 0 < t) : (toQ (pt x y t ht)).imI = y := rfl
theorem toQ_pt_imJ (x y t : ℝ) (ht : 0 < t) : (toQ (pt x y t ht)).imJ = t := rfl

/-- The component equations at a fixed point, in the form `fixed_point_real` takes. -/
theorem fixed_point_components (g : SL(2, ℂ)) (p : H3) (hfix : g • p = p) :
    ((toQ p).re * ((g 1 0).re * (toQ p).re - (g 1 0).im * (toQ p).imI + (g 1 1).re)
        - (toQ p).imI * ((g 1 0).re * (toQ p).imI + (g 1 0).im * (toQ p).re + (g 1 1).im)
        - (toQ p).imJ * ((g 1 0).re * (toQ p).imJ)
      = (g 0 0).re * (toQ p).re - (g 0 0).im * (toQ p).imI + (g 0 1).re) ∧
    ((toQ p).re * ((g 1 0).re * (toQ p).imI + (g 1 0).im * (toQ p).re + (g 1 1).im)
        + (toQ p).imI * ((g 1 0).re * (toQ p).re - (g 1 0).im * (toQ p).imI + (g 1 1).re)
        + (toQ p).imJ * ((g 1 0).im * (toQ p).imJ)
      = (g 0 0).re * (toQ p).imI + (g 0 0).im * (toQ p).re + (g 0 1).im) ∧
    ((toQ p).imJ * (2 * ((g 1 0).re * (toQ p).re - (g 1 0).im * (toQ p).imI) + (g 1 1).re)
      = (g 0 0).re * (toQ p).imJ) ∧
    (-((toQ p).imJ * (g 1 1).im) = (g 0 0).im * (toQ p).imJ) ∧
    (((g 1 0).re * (toQ p).re - (g 1 0).im * (toQ p).imI + (g 1 1).re) ^ 2
        + ((g 1 0).re * (toQ p).imI + (g 1 0).im * (toQ p).re + (g 1 1).im) ^ 2
        + ((g 1 0).re * (toQ p).imJ) ^ 2 + ((g 1 0).im * (toQ p).imJ) ^ 2 = 1) := by
  have hK := toQ_imK p
  have hM0 := denom_ne_zero (sl2_row_ne_zero g) hK p.2
  have hq : toQ p * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) =
      ((g 0 0 : ℂ) : ℍ) * toQ p + ((g 0 1 : ℂ) : ℍ) := by
    have e : mobiusQ g (toQ p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) =
        ((g 0 0 : ℂ) : ℍ) * toQ p + ((g 0 1 : ℂ) : ℍ) := by
      unfold mobiusQ
      exact inv_mul_cancel_right₀ hM0 _
    rwa [← toQ_smul, hfix] at e
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
  exact ⟨by linear_combination e₀, by linear_combination e₁, by linear_combination e₂,
    by linear_combination e₃, by linear_combination hN⟩

/-- **An element acting trivially is `±1`**: fixing `(0,0,1)` and `(0,0,2)` forces
`b = c = 0`, fixing `(1,0,1)` then makes the diagonal real, and the determinant does the rest. -/
theorem coe_eq_pm_one_of_forall_smul_eq {g : SL(2, ℂ)} (hall : ∀ q : H3, g • q = q) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  obtain ⟨e₀, e₁, e₂, e₃, hN⟩ := fixed_point_components g (pt 0 0 1 one_pos) (hall _)
  obtain ⟨f₀, f₁, -, -, -⟩ := fixed_point_components g (pt 0 0 2 two_pos) (hall _)
  obtain ⟨-, k₁, -, -, -⟩ := fixed_point_components g (pt 1 0 1 one_pos) (hall _)
  simp only [toQ_pt_re, toQ_pt_imI, toQ_pt_imJ] at e₀ e₁ e₂ e₃ hN f₀ f₁ k₁
  have hc₁ : (g 1 0).re = 0 := by linear_combination (e₀ - f₀) / 3
  have hc₂ : (g 1 0).im = 0 := by linear_combination (f₁ - e₁) / 3
  have hb₁ : (g 0 1).re = 0 := by linear_combination -e₀ - hc₁
  have hb₂ : (g 0 1).im = 0 := by linear_combination -e₁ + hc₂
  have hd₂ : (g 1 1).im = 0 := by linear_combination (k₁ - e₃ - 2 * hc₂ + hb₂) / 2
  have ha₂ : (g 0 0).im = 0 := by linear_combination -e₃ - hd₂
  have ha₁ : (g 0 0).re = (g 1 1).re := by linear_combination -e₂
  have hd₁ : (g 1 1).re ^ 2 = 1 := by
    have : (g 1 1).re ^ 2 + (g 1 1).im ^ 2 = 1 := by
      linear_combination hN - (g 1 0).re * hc₁ - (g 1 0).im * hc₂
    rw [hd₂] at this
    linear_combination this
  have hb : g 0 1 = 0 := Complex.ext (by simpa using hb₁) (by simpa using hb₂)
  have hc : g 1 0 = 0 := Complex.ext (by simpa using hc₁) (by simpa using hc₂)
  have hd : (g 1 1).re = 1 ∨ (g 1 1).re = -1 := by
    have h2 : ((g 1 1).re - 1) * ((g 1 1).re + 1) = 0 := by linear_combination hd₁
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hd with h | h
  · have e11 : g 1 1 = 1 := Complex.ext (by simpa using h) (by simpa using hd₂)
    have e00 : g 0 0 = 1 := Complex.ext (by simpa [ha₁] using h) (by simpa using ha₂)
    refine Or.inl ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, hb, hc, e11]
  · have e11 : g 1 1 = -1 := Complex.ext (by simpa using h) (by simpa using hd₂)
    have e00 : g 0 0 = -1 := Complex.ext (by simpa [ha₁] using h) (by simpa using ha₂)
    refine Or.inr ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, hb, hc, e11]

theorem neg_one_mem_picard : (-1 : SL(2, ℂ)) ∈ picard := by
  rw [mem_picard_iff]
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-1, by simp [Matrix.SpecialLinearGroup.coe_neg]⟩
  · exact ⟨0, by simp [Matrix.SpecialLinearGroup.coe_neg]⟩
  · exact ⟨0, by simp [Matrix.SpecialLinearGroup.coe_neg]⟩
  · exact ⟨-1, by simp [Matrix.SpecialLinearGroup.coe_neg]⟩

/-- `-1` as an element of the Picard group. -/
noncomputable def negOnePicard : picard := ⟨-1, neg_one_mem_picard⟩

theorem mem_picardKer_iff {g : picard} :
    g ∈ picardKer ↔ (g : SL(2, ℂ)) = 1 ∨ (g : SL(2, ℂ)) = -1 := by
  have key : g ∈ picardKer ↔ ∀ q : H3, (g : SL(2, ℂ)) • q = q := by
    rw [picardKer, MonoidHom.mem_ker]
    constructor
    · intro h q
      have := congrArg (fun σ : Equiv.Perm H3 => σ q) h
      simpa [MulAction.toPermHom_apply] using this
    · intro h
      refine Equiv.ext fun q => ?_
      simpa [MulAction.toPermHom_apply] using h q
  rw [key]
  constructor
  · intro h
    rcases coe_eq_pm_one_of_forall_smul_eq h with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext (by rw [h1, Matrix.SpecialLinearGroup.coe_neg]; simp))
  · intro h q
    refine smul_eq_self_of_coe_eq_pm_one ?_ q
    rcases h with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [h, Matrix.SpecialLinearGroup.coe_neg]; simp)

theorem picardKer_eq_zpowers : picardKer = Subgroup.zpowers negOnePicard := by
  refine le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.2 (mem_picardKer_iff.2 (Or.inr rfl)))
  rw [Subgroup.mem_zpowers_iff]
  rcases mem_picardKer_iff.1 hg with h | h
  · exact ⟨0, by rw [zpow_zero]; exact (Subtype.ext h).symm⟩
  · exact ⟨1, by rw [zpow_one]; exact (Subtype.ext h).symm⟩

theorem negOnePicard_ne_one : negOnePicard ≠ 1 := by
  intro h
  have := congrArg (fun g : picard => ((g : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  simp [negOnePicard] at this
  norm_num at this

theorem card_picardKer : Nat.card picardKer = 2 := by
  rw [picardKer_eq_zpowers, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ negOnePicard_ne_one
  apply Subtype.ext
  apply Subtype.ext
  simp [negOnePicard]

/-- `-1 ∉ Γ(2 + i)`: `-1 ≢ 1 (mod 2 + i)`, since `5 ∤ 2`. -/
theorem neg_one_notMem_gammaTwoI : (-1 : SL(2, ℂ)) ∉ gammaTwoI := by
  rintro ⟨h, hh, hmap⟩
  have hneg : h = -1 := by
    apply sl2Map_injective
    rw [hmap]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_neg]
    fin_cases i <;> fin_cases j <;> simp
  subst hneg
  have hmem := sub_one_mem_of_mem_gammaTwoIZ hh 0
  have e : (-1 : SL(2, GaussianInt)) 0 0 - 1 = ((-2 : ℤ) : GaussianInt) := by
    simp [Matrix.SpecialLinearGroup.coe_neg]
    norm_num
  rw [e, intCast_mem_idealTwoI_iff] at hmem
  norm_num at hmem
end KernelPmOne

section IndexSixty

/-- `SL(2, ℤ[i]) ≅ picard`. -/
noncomputable def picardEquiv : SL(2, GaussianInt) ≃* picard := MonoidHom.ofInjective sl2Map_injective

theorem picardEquiv_apply_coe (h : SL(2, GaussianInt)) :
    ((picardEquiv h : picard) : SL(2, ℂ)) = Matrix.SpecialLinearGroup.map GaussianInt.toComplex h :=
  MonoidHom.ofInjective_apply sl2Map_injective

theorem gammaTwoI_subgroupOf_eq :
    gammaTwoI.subgroupOf picard = gammaTwoIZ.map (picardEquiv : SL(2, GaussianInt) →* picard) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, gammaTwoI, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hx⟩
    exact ⟨h, hh, Subtype.ext (by rw [← hx]; exact picardEquiv_apply_coe h)⟩
  · rintro ⟨h, hh, hx⟩
    refine ⟨h, hh, ?_⟩
    rw [← picardEquiv_apply_coe]
    exact congrArg Subtype.val hx

instance gammaTwoI_subgroupOf_normal : (gammaTwoI.subgroupOf picard).Normal := by
  rw [gammaTwoI_subgroupOf_eq]
  exact (MonoidHom.normal_ker _).map _ picardEquiv.surjective

/-- **`[picard : Γ(2+i)] = 120`.** -/
theorem index_gammaTwoI_subgroupOf : (gammaTwoI.subgroupOf picard).index = 120 := by
  rw [gammaTwoI_subgroupOf_eq, Subgroup.index_map_equiv, index_gammaTwoIZ]

theorem gammaTwoI_inf_picardKer : gammaTwoI.subgroupOf picard ⊓ picardKer = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx, hk⟩ := hx
  rcases mem_picardKer_iff.1 hk with h | h
  · exact Subtype.ext h
  · rw [Subgroup.mem_subgroupOf, h] at hx
    exact absurd hx neg_one_notMem_gammaTwoI

/-- **The index of `Γ(2+i)` in the effective Picard group is `60`**: `120` for `±1`. -/
theorem index_gammaTwoIEff : gammaTwoIEff.index = 60 := by
  have h1 : gammaTwoIEff.index = (gammaTwoI.subgroupOf picard ⊔ picardKer).index := by
    rw [gammaTwoIEff, Subgroup.index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
  have h2 := Subgroup.relIndex_mul_index
    (le_sup_left : gammaTwoI.subgroupOf picard ≤ gammaTwoI.subgroupOf picard ⊔ picardKer)
  have h3 : (gammaTwoI.subgroupOf picard).relIndex (gammaTwoI.subgroupOf picard ⊔ picardKer)
      = 2 := by
    rw [sup_comm, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right,
      gammaTwoI_inf_picardKer, Subgroup.relIndex_bot_left, card_picardKer]
  rw [h3, index_gammaTwoI_subgroupOf] at h2
  rw [h1]
  omega


end IndexSixty

end Thurston23

open MeasureTheory in
theorem solution : Thurston23.gammaTwoIEff.index = 60 :=
  Thurston23.index_gammaTwoIEff
