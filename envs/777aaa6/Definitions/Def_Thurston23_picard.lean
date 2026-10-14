-- Prove2me | Definitions.Def_Thurston23_picard
-- name    : Thurston23_picard
-- status  : Definition
-- author  : @t4v1
-- created : 2026-09-13T16:26:03.695981+00:00
-- url     : https://prove2.me/theorems/4a700f8d-6f2e-4d4d-a18b-d05d0be2a9d3
-- title:
--   The Picard group $\mathrm{SL}_2(\mathbb{Z}[i])$, its congruence subgroup $\Gamma(2+i)$, the half box, and the effective Picard group
-- statement:
--   The objects of the arithmetic example on top of `Thurston23_mobius`: the Picard group `picard`, the subgroup of $\mathrm{SL}_2(\mathbb{C})$ of matrices with Gaussian integer entries; the ideal $(2+i)$ of $\mathbb{Z}[i]$, of norm $5$, with the finiteness of $\mathbb{Z}[i]/(2+i)$; the principal congruence subgroup `gammaTwoIZ` of $\mathrm{SL}_2(\mathbb{Z}[i])$, the kernel of reduction modulo $2+i$, and its image `gammaTwoI` in $\mathrm{SL}_2(\mathbb{C})$; the closed half box
--
--   $$B = \{(x,y,t) : |x| \le \tfrac12,\ 0 \le y \le \tfrac12,\ x^2 + y^2 + t^2 \ge 1\}$$
--
--   (`halfBox`) and its interior (`halfBoxOpen`), the fundamental domain of the Picard group modulo $\pm 1$; the kernel `picardKer` of the Picard action on hyperbolic space, the effective Picard group `PicardEff = picard ⧸ picardKer` with its induced action, and the image `gammaTwoIEff` of $\Gamma(2+i)$ in it.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/Thurston23.lean#L1250-L1253, #L1547-L1579, #L2257-L2260, #L2653-L2654, #L2787-L2811, #L2872-L2874.

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius

/-!
The Picard group `SL(2, ℤ[i])` inside `SL(2, ℂ)`, its principal congruence subgroup `Γ(2 + i)`,
the closed half box `|x| ≤ ½`, `0 ≤ y ≤ ½`, `|q| ≥ 1` (the fundamental domain of the Picard
group modulo `±1`), the kernel of the action and the effective Picard group `PicardEff`, and the
image `gammaTwoIEff` of `Γ(2 + i)` in it. Taken verbatim from the mission's source file
`Thurston23.lean`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

open Set MatrixGroups Quaternion Pointwise

/-- The Picard group `SL(2, ℤ[i])`, as the subgroup of `SL(2, ℂ)` of matrices with Gaussian
integer entries (`mem_picard_iff`). -/
noncomputable def picard : Subgroup SL(2, ℂ) :=
  (Matrix.SpecialLinearGroup.map GaussianInt.toComplex).range

/-- The ideal `(2 + i)` of `ℤ[i]`, of norm `5`. -/
def idealTwoI : Ideal GaussianInt := Ideal.span {⟨2, 1⟩}

/-- Every Gaussian integer is congruent modulo `2 + i` to one of `0, …, 4`, because
`i ≡ -2` and `5 = (2 + i)(2 - i)`. -/
instance : Finite (GaussianInt ⧸ idealTwoI) := by
  refine Set.finite_univ_iff.1 (((Set.finite_Icc (0 : ℤ) 4).image
    fun n : ℤ => Ideal.Quotient.mk idealTwoI (n : GaussianInt)).subset ?_)
  rintro x -
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(z.re - 2 * z.im) % 5, ⟨by omega, by omega⟩, ?_⟩
  show Ideal.Quotient.mk idealTwoI (((z.re - 2 * z.im) % 5 : ℤ) : GaussianInt) =
    Ideal.Quotient.mk idealTwoI z
  rw [Ideal.Quotient.eq, idealTwoI, Ideal.mem_span_singleton]
  refine ⟨⟨-z.im - 2 * ((z.re - 2 * z.im) / 5), (z.re - 2 * z.im) / 5⟩, ?_⟩
  ext <;> (simp; try omega)

instance : Finite SL(2, GaussianInt ⧸ idealTwoI) :=
  Finite.of_injective (fun (g : SL(2, GaussianInt ⧸ idealTwoI)) (i j : Fin 2) => g i j)
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

/-- The principal congruence subgroup `Γ(2 + i)` of `SL(2, ℤ[i])`: the kernel of reduction
modulo `2 + i`. -/
def gammaTwoIZ : Subgroup SL(2, GaussianInt) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealTwoI)).ker

/-- `Γ(2 + i)` as a subgroup of `SL(2, ℂ)`, inside the Picard group. -/
noncomputable def gammaTwoI : Subgroup SL(2, ℂ) :=
  gammaTwoIZ.map (Matrix.SpecialLinearGroup.map GaussianInt.toComplex)

theorem gammaTwoI_le_picard : gammaTwoI ≤ picard := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

/-- The open half box: `|x| < ½`, `0 < y < ½`, `|q| > 1`. Its closure is the
standard fundamental domain of the Picard group modulo `±1`. -/
def halfBoxOpen : Set H3 :=
  {p | |p.1 0| < 1 / 2 ∧ 0 < p.1 1 ∧ p.1 1 < 1 / 2 ∧ 1 < N p.1}

/-- The closed half box: `|x| ≤ ½`, `0 ≤ y ≤ ½`, `|q| ≥ 1`. -/
def halfBox : Set H3 := {p | |p.1 0| ≤ 1 / 2 ∧ 0 ≤ p.1 1 ∧ p.1 1 ≤ 1 / 2 ∧ 1 ≤ N p.1}

/-- The elements of the Picard group acting trivially on `H3`. It is `{±1}`, but
nothing below needs that: as a kernel it is normal for free. -/
noncomputable def picardKer : Subgroup picard := MonoidHom.ker (MulAction.toPermHom picard H3)

instance picardKer.instNormal : picardKer.Normal :=
  MonoidHom.normal_ker (MulAction.toPermHom picard H3)

/-- The Picard group made effective: the quotient by the kernel of its action, so
that `±1` is divided out. This is the group the half box is a fundamental domain
for. -/
abbrev PicardEff : Type := picard ⧸ picardKer

noncomputable instance : MulAction PicardEff H3 :=
  MulAction.compHom H3 (QuotientGroup.kerLift (MulAction.toPermHom picard H3))

theorem PicardEff.mk_smul (g : picard) (p : H3) :
    (QuotientGroup.mk g : PicardEff) • p = (g : SL(2, ℂ)) • p := rfl

theorem PicardEff.mk_smul_set (g : picard) (S : Set H3) :
    (QuotientGroup.mk g : PicardEff) • S = (g : SL(2, ℂ)) • S := rfl

theorem PicardEff.measurePreserving (q : PicardEff) :
    MeasurePreserving (fun p : H3 => q • p) hvol hvol := by
  induction q using QuotientGroup.induction_on with
  | H g => exact measurePreserving_smul (g : SL(2, ℂ))

/-- The image of `Γ(2+i)` in the effectively acting Picard group. -/
noncomputable def gammaTwoIEff : Subgroup PicardEff :=
  (gammaTwoI.subgroupOf picard).map (QuotientGroup.mk' picardKer)

end Thurston23


