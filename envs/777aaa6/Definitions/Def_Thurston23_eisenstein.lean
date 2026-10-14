-- Prove2me | Definitions.Def_Thurston23_eisenstein
-- name    : Thurston23_eisenstein
-- status  : Definition
-- author  : @t4v1
-- created : 2026-09-14T16:22:11.811946+00:00
-- url     : https://prove2.me/theorems/39544c68-9ff4-4f8c-a78d-1eeac13b457d
-- title:
--   The Bianchi group $\mathrm{SL}_2(\mathbb{Z}[\omega])$, its congruence subgroup of level $3+\omega$, and the box over a rhombus
-- statement:
--   The objects of the Eisenstein example, on top of `Thurston23_mobius`. The ring `EisInt` of Eisenstein integers $a + b\omega$, $\omega = e^{2\pi i/3}$, with its embedding `EisInt.toComplex` in $\mathbb{C}$ (the ring structure is pulled back along this embedding). The Bianchi group `eisGroup`, the matrices of $\mathrm{SL}_2(\mathbb{C})$ with entries in $\mathbb{Z}[\omega]$; the prime ideal `idealP` $= (3+\omega)$, of norm $7$; the principal congruence subgroup `gammaSevenZ` of $\mathrm{SL}_2(\mathbb{Z}[\omega])$, the kernel of reduction modulo $3+\omega$, and its image `gammaSeven` in $\mathrm{SL}_2(\mathbb{C})$. The rhombus `eisBase` $= \{0 \le x \le \tfrac12,\ 0 \le x + \sqrt3\,y \le 1\}$ and the box over it,
--
--   $$B = \{(x,y,t) : 0 \le x \le \tfrac12,\ 0 \le x + \sqrt3\,y \le 1,\ x^2 + y^2 + t^2 \ge 1\}$$
--
--   (`eisBox`, with its interior `eisBoxOpen`), the fundamental domain of the Bianchi group modulo the kernel of its action. Finally the kernel `eisKer` of the action on hyperbolic space, the effective Bianchi group `EisEff`, and the image `gammaSevenEff` of $\Gamma(3+\omega)$ in it.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7 (Bianchi groups and Humbert's formula). Formalisation: https://github.com/t4v1/thurston23/blob/main/Thurston23Eisenstein.lean

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius

/-!
The Bianchi group `SL(2, ℤ[ω])`, `ω = e^{2πi/3}`, its congruence subgroup of level `3 + ω`,
the box over the rhombus `0 ≤ x ≤ ½`, `0 ≤ x + √3 y ≤ 1`, and the effective Bianchi group.
Taken verbatim from the mission's source file `Thurston23Eisenstein.lean`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

section EisensteinRing

/-- `ω = e^{2πi/3} = -½ + (√3/2) i`. -/
noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

/-- The Eisenstein integer `a + b ω`. -/
@[ext] structure EisInt where
  a : ℤ
  b : ℤ
deriving DecidableEq

namespace EisInt

instance : Zero EisInt := ⟨⟨0, 0⟩⟩
instance : One EisInt := ⟨⟨1, 0⟩⟩
instance : Add EisInt := ⟨fun z w => ⟨z.a + w.a, z.b + w.b⟩⟩
instance : Neg EisInt := ⟨fun z => ⟨-z.a, -z.b⟩⟩
instance : Sub EisInt := ⟨fun z w => ⟨z.a - w.a, z.b - w.b⟩⟩
/-- `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) ω`, since `ω² = -1 - ω`. -/
instance : Mul EisInt := ⟨fun z w => ⟨z.a * w.a - z.b * w.b, z.a * w.b + z.b * w.a - z.b * w.b⟩⟩
instance : SMul ℕ EisInt := ⟨fun n z => ⟨n * z.a, n * z.b⟩⟩
instance : SMul ℤ EisInt := ⟨fun n z => ⟨n * z.a, n * z.b⟩⟩
instance : NatCast EisInt := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast EisInt := ⟨fun n => ⟨n, 0⟩⟩
instance : Pow EisInt ℕ := ⟨fun z n => npowRec n z⟩

/-- The embedding `a + bω ↦ a + b ω` in `ℂ`. -/
noncomputable def toC (z : EisInt) : ℂ := (z.a : ℂ) + (z.b : ℂ) * omega

theorem toC_re (z : EisInt) : (toC z).re = z.a - z.b / 2 := by
  simp only [toC, omega, Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  ring

theorem toC_im (z : EisInt) : (toC z).im = z.b * (Real.sqrt 3 / 2) := by
  simp only [toC, omega, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
  ring

theorem toC_ext {z w : ℂ} (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w := Complex.ext h1 h2

theorem toC_injective : Function.Injective toC := by
  intro z w h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  rw [toC_im, toC_im] at him
  rw [toC_re, toC_re] at hre
  have hb : (z.b : ℝ) = w.b := by
    have hs : Real.sqrt 3 / 2 ≠ 0 := by have := sqrt3_pos; positivity
    exact mul_right_cancel₀ hs him
  have hb' : z.b = w.b := by exact_mod_cast hb
  have ha : (z.a : ℝ) = w.a := by rw [hb] at hre; linarith
  exact EisInt.ext (by exact_mod_cast ha) hb'

theorem toC_zero : toC 0 = 0 := by
  apply toC_ext
  · rw [toC_re]; show ((0:ℤ):ℝ) - ((0:ℤ):ℝ) / 2 = 0; simp
  · rw [toC_im]; show ((0:ℤ):ℝ) * _ = 0; simp

theorem toC_one : toC 1 = 1 := by
  apply toC_ext
  · rw [toC_re]; show ((1:ℤ):ℝ) - ((0:ℤ):ℝ) / 2 = 1; simp
  · rw [toC_im]; show ((0:ℤ):ℝ) * _ = 0; simp

theorem toC_add (z w : EisInt) : toC (z + w) = toC z + toC w := by
  apply toC_ext
  · rw [Complex.add_re, toC_re, toC_re, toC_re]
    show (((z.a + w.a : ℤ)) : ℝ) - ((z.b + w.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.add_im, toC_im, toC_im, toC_im]
    show ((z.b + w.b : ℤ) : ℝ) * _ = _
    push_cast; ring

theorem toC_neg (z : EisInt) : toC (-z) = -toC z := by
  apply toC_ext
  · rw [Complex.neg_re, toC_re, toC_re]
    show ((-z.a : ℤ) : ℝ) - ((-z.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.neg_im, toC_im, toC_im]
    show ((-z.b : ℤ) : ℝ) * _ = _
    push_cast; ring

theorem toC_sub (z w : EisInt) : toC (z - w) = toC z - toC w := by
  apply toC_ext
  · rw [Complex.sub_re, toC_re, toC_re, toC_re]
    show (((z.a - w.a : ℤ)) : ℝ) - ((z.b - w.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.sub_im, toC_im, toC_im, toC_im]
    show ((z.b - w.b : ℤ) : ℝ) * _ = _
    push_cast; ring

theorem toC_mul (z w : EisInt) : toC (z * w) = toC z * toC w := by
  apply toC_ext
  · rw [Complex.mul_re, toC_re, toC_re, toC_re, toC_im, toC_im]
    show ((z.a * w.a - z.b * w.b : ℤ) : ℝ) - ((z.a * w.b + z.b * w.a - z.b * w.b : ℤ) : ℝ) / 2 = _
    push_cast
    linear_combination ((z.b : ℝ) * w.b / 4) * sqrt3_sq
  · rw [Complex.mul_im, toC_im, toC_im, toC_im, toC_re, toC_re]
    show ((z.a * w.b + z.b * w.a - z.b * w.b : ℤ) : ℝ) * _ = _
    push_cast
    ring

theorem toC_nsmul (n : ℕ) (z : EisInt) : toC (n • z) = n • toC z := by
  rw [nsmul_eq_mul]
  apply toC_ext
  · rw [Complex.mul_re, toC_re, toC_re, toC_im]
    show ((n * z.a : ℤ) : ℝ) - ((n * z.b : ℤ) : ℝ) / 2 = _
    simp; ring
  · rw [Complex.mul_im, toC_im, toC_im, toC_re]
    show ((n * z.b : ℤ) : ℝ) * _ = _
    simp; ring

theorem toC_zsmul (n : ℤ) (z : EisInt) : toC (n • z) = n • toC z := by
  rw [zsmul_eq_mul]
  apply toC_ext
  · rw [Complex.mul_re, toC_re, toC_re, toC_im]
    show ((n * z.a : ℤ) : ℝ) - ((n * z.b : ℤ) : ℝ) / 2 = _
    simp; ring
  · rw [Complex.mul_im, toC_im, toC_im, toC_re]
    show ((n * z.b : ℤ) : ℝ) * _ = _
    simp; ring

theorem toC_pow (z : EisInt) (n : ℕ) : toC (z ^ n) = toC z ^ n := by
  induction n with
  | zero => exact toC_one
  | succ n ih =>
    show toC (z ^ n * z) = _
    rw [toC_mul, ih, pow_succ]

theorem toC_natCast (n : ℕ) : toC n = n := by
  apply toC_ext
  · rw [toC_re]; show ((n : ℤ) : ℝ) - ((0 : ℤ) : ℝ) / 2 = _; simp
  · rw [toC_im]; show ((0 : ℤ) : ℝ) * _ = _; simp

theorem toC_intCast (n : ℤ) : toC n = n := by
  apply toC_ext
  · rw [toC_re]; show ((n : ℤ) : ℝ) - ((0 : ℤ) : ℝ) / 2 = _; simp
  · rw [toC_im]; show ((0 : ℤ) : ℝ) * _ = _; simp

noncomputable instance : CommRing EisInt :=
  toC_injective.commRing toC toC_zero toC_one toC_add toC_mul toC_neg toC_sub toC_nsmul
    toC_zsmul toC_pow toC_natCast toC_intCast

/-- The embedding as a ring homomorphism. -/
noncomputable def toComplex : EisInt →+* ℂ where
  toFun := toC
  map_one' := toC_one
  map_mul' := toC_mul
  map_zero' := toC_zero
  map_add' := toC_add

@[simp] theorem toComplex_apply (z : EisInt) : toComplex z = toC z := rfl

/-- `|a + bω|² = a² - ab + b²`. -/
theorem normSq_toC (z : EisInt) :
    Complex.normSq (toC z) = ((z.a ^ 2 - z.a * z.b + z.b ^ 2 : ℤ) : ℝ) := by
  rw [Complex.normSq_apply, toC_re, toC_im]
  push_cast
  linear_combination ((z.b : ℝ) ^ 2 / 4) * sqrt3_sq

/-- The conjugate `a + bω² = (a - b) - bω`. -/
def conjE (z : EisInt) : EisInt := ⟨z.a - z.b, -z.b⟩

theorem toC_conjE (z : EisInt) : toC (conjE z) = (starRingEnd ℂ) (toC z) := by
  apply toC_ext
  · rw [Complex.conj_re, toC_re, toC_re]
    show ((z.a - z.b : ℤ) : ℝ) - ((-z.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.conj_im, toC_im, toC_im]
    show ((-z.b : ℤ) : ℝ) * _ = _
    push_cast; ring

end EisInt

end EisensteinRing

section EisDefs

open Set MatrixGroups Quaternion Pointwise

/-- The complex coordinate `x + iy` of a point of `H3`. -/
noncomputable def zc (p : H3) : ℂ := ⟨p.1 0, p.1 1⟩

@[simp] theorem zc_re (p : H3) : (zc p).re = p.1 0 := rfl

@[simp] theorem zc_im (p : H3) : (zc p).im = p.1 1 := rfl

/-- The Bianchi group `SL(2, ℤ[ω])` inside `SL(2, ℂ)`. -/
noncomputable def eisGroup : Subgroup SL(2, ℂ) :=
  (Matrix.SpecialLinearGroup.map EisInt.toComplex).range

/-- The prime ideal `(3 + ω)` of `ℤ[ω]`, of norm `7`. -/
noncomputable def idealP : Ideal EisInt := Ideal.span {⟨3, 1⟩}

/-- `a + bω ∈ (3 + ω)` iff `7 ∣ 2a + b`: `(3 + ω)(c + dω) = (3c - d) + (c + 2d)ω`. -/
theorem mem_idealP_iff (z : EisInt) : z ∈ idealP ↔ (7 : ℤ) ∣ 2 * z.a + z.b := by
  rw [idealP, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    change (7 : ℤ) ∣ 2 * (3 * c.a - 1 * c.b) + (3 * c.b + 1 * c.a - 1 * c.b)
    exact ⟨c.a, by ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, 3 * k - z.a⟩, ?_⟩
    apply EisInt.ext
    · change z.a = 3 * k - 1 * (3 * k - z.a); ring
    · change z.b = 3 * (3 * k - z.a) + 1 * k - 1 * (3 * k - z.a); omega

/-- Every Eisenstein integer is congruent modulo `3 + ω` to one of `0, …, 6`: `ω ≡ -3`. -/
instance : Finite (EisInt ⧸ idealP) := by
  refine Set.finite_univ_iff.1 (((Set.finite_Icc (0 : ℤ) 6).image
    fun n : ℤ => Ideal.Quotient.mk idealP (n : EisInt)).subset ?_)
  rintro x -
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(z.a - 3 * z.b) % 7, ⟨by omega, by omega⟩, ?_⟩
  show Ideal.Quotient.mk idealP (((z.a - 3 * z.b) % 7 : ℤ) : EisInt) = Ideal.Quotient.mk idealP z
  rw [Ideal.Quotient.eq, mem_idealP_iff]
  change (7 : ℤ) ∣ 2 * ((z.a - 3 * z.b) % 7 - z.a) + (0 - z.b)
  omega

instance : Finite SL(2, EisInt ⧸ idealP) :=
  Finite.of_injective (fun (g : SL(2, EisInt ⧸ idealP)) (i j : Fin 2) => g i j)
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

/-- The principal congruence subgroup of level `3 + ω` of `SL(2, ℤ[ω])`. -/
noncomputable def gammaSevenZ : Subgroup SL(2, EisInt) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealP)).ker

/-- The same subgroup inside `SL(2, ℂ)`. -/
noncomputable def gammaSeven : Subgroup SL(2, ℂ) :=
  gammaSevenZ.map (Matrix.SpecialLinearGroup.map EisInt.toComplex)

/-- The closed rhombus `0 ≤ x ≤ ½`, `0 ≤ x + √3 y ≤ 1`. -/
def eisBase (w : ℂ) : Prop :=
  0 ≤ w.re ∧ w.re ≤ 1 / 2 ∧ 0 ≤ w.re + Real.sqrt 3 * w.im ∧ w.re + Real.sqrt 3 * w.im ≤ 1

/-- The open rhombus. -/
def eisBaseOpen (w : ℂ) : Prop :=
  0 < w.re ∧ w.re < 1 / 2 ∧ 0 < w.re + Real.sqrt 3 * w.im ∧ w.re + Real.sqrt 3 * w.im < 1

/-- The closed box over the rhombus, above the unit sphere. -/
def eisBox : Set H3 := {p | eisBase (zc p) ∧ 1 ≤ N p.1}

/-- The open box. -/
def eisBoxOpen : Set H3 := {p | eisBaseOpen (zc p) ∧ 1 < N p.1}

noncomputable def eisKer : Subgroup eisGroup := MonoidHom.ker (MulAction.toPermHom eisGroup H3)

instance eisKer.instNormal : eisKer.Normal :=
  MonoidHom.normal_ker (MulAction.toPermHom eisGroup H3)

/-- The Bianchi group made effective: the quotient by the kernel of its action, so
that `±1` is divided out. This is the group the box is a fundamental domain
for. -/
abbrev EisEff : Type := eisGroup ⧸ eisKer
noncomputable instance : MulAction EisEff H3 :=
  MulAction.compHom H3 (QuotientGroup.kerLift (MulAction.toPermHom eisGroup H3))

theorem EisEff.mk_smul (g : eisGroup) (p : H3) :
    (QuotientGroup.mk g : EisEff) • p = (g : SL(2, ℂ)) • p := rfl

theorem EisEff.mk_smul_set (g : eisGroup) (S : Set H3) :
    (QuotientGroup.mk g : EisEff) • S = (g : SL(2, ℂ)) • S := rfl

theorem EisEff.measurePreserving (q : EisEff) :
    MeasurePreserving (fun p : H3 => q • p) hvol hvol := by
  induction q using QuotientGroup.induction_on with
  | H g => exact measurePreserving_smul (g : SL(2, ℂ))

/-- The image of `Γ(3+ω)` in the effectively acting Bianchi group. -/
noncomputable def gammaSevenEff : Subgroup EisEff :=
  (gammaSeven.subgroupOf eisGroup).map (QuotientGroup.mk' eisKer)

end EisDefs

end Thurston23


