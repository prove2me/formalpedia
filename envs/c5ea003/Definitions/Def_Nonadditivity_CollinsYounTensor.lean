-- Prove2me | Definitions.Def_Nonadditivity_CollinsYounTensor
-- name    : Nonadditivity_CollinsYounTensor
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:38:34.126449+00:00
-- url     : https://prove2.me/theorems/a57c62ad-564d-42db-9839-73c56a3cf088
-- title:
--   Operator valued length-two regular polynomials
-- statement:
--   Let $A$ be a finite generator set and $E$ a complex Hilbert space. For a matrix $B=(B_{ij})$ of bounded operators on $E$, the local polynomial is $\sum_{i,j}\widetilde B_{ij}\lambda_{g_i^{-1}g_j}$ on $\ell^2(F_A;E)$, with coefficient length $\bigl(\sum_{i,j}\|B_{ij}\|^2\bigr)^{1/2}$. Coordinate masks and creation shifts give its creation, annihilation, and one-cancellation components. When $B_{ii}=0$ for every $i$, the proved estimate bounds the polynomial norm by three times the coefficient length.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/CollinsYounTensor.lean#L33-L538

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularRestriction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! # Operator coefficients in the length-two regular estimate

The creation and annihilation decomposition acts on the genuine vector-valued
space `lp (fun _ : FreeGroup α => E) 2`.  Arbitrary bounded operators on the
coefficient Hilbert space commute with the coordinate projections and shifts.
The three cancellation components are each bounded by the square root of the
sum of the squared operator norms of the coefficients.  This supplies the
analytic induction step for the product-group Collins--Youn estimate.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.CollinsYounTensor
open FreeCreation (Letter Cone letter flip cone_disjoint cone_shift_iff letter_flip)
open RegularCoefficientEnergy (VectorHilbert liftOperator)
open CollinsYoun (norm_sum_sq_of_inner_zero)
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
section Mask

variable {G : Type*}

/-- An actual coordinate projection on the regular Hilbert space. -/
def maskFunction (P : G → Prop) (f : VectorHilbert G E) : VectorHilbert G E :=
  ⟨fun x => if P x then f x else 0, by
    classical
    apply memℓp_gen
    apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun x => ?_) (f.property.summable (by norm_num))
    split_ifs <;> simp⟩

@[simp] theorem maskFunction_apply (P : G → Prop) (f : VectorHilbert G E) (x : G) :
    maskFunction (E := E) P f x = if P x then f x else 0 := rfl

theorem maskFunction_norm_le (P : G → Prop) (f : VectorHilbert G E) :
    ‖maskFunction (E := E) P f‖ ≤ ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg f)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  apply Summable.tsum_le_tsum
    (fun x => ?_) ((maskFunction (E := E) P f).property.summable (by norm_num))
    (f.property.summable (by norm_num))
  classical
  simp only [maskFunction_apply]
  split_ifs <;> simp

def maskLinear (P : G → Prop) : VectorHilbert G E →ₗ[ℂ] VectorHilbert G E where
  toFun := maskFunction (E := E) P
  map_add' := by
    intro f h
    ext x
    classical
    simp only [maskFunction_apply, lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c f
    ext x
    classical
    simp only [maskFunction_apply, lp.coeFn_smul, Pi.smul_apply]
    split_ifs <;> simp

/-- The coordinate mask is a genuine bounded linear projection. -/
def mask (P : G → Prop) : VectorHilbert G E →L[ℂ] VectorHilbert G E :=
  (maskLinear (E := E) P).mkContinuous 1 (by
    intro f
    simpa [maskLinear] using maskFunction_norm_le P f)

@[simp] theorem mask_apply (P : G → Prop) (f : VectorHilbert G E) (x : G) :
    mask (E := E) P f x = if P x then f x else 0 := rfl

theorem mask_norm_le (P : G → Prop) (f : VectorHilbert G E) : ‖mask (E := E) P f‖ ≤ ‖f‖ :=
  maskFunction_norm_le P f

theorem mask_adjoint (P : G → Prop) : (mask (E := E) P).adjoint = mask (E := E) P := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (∑' x, inner ℂ (f x) (mask (E := E) P h x)) =
    ∑' x, inner ℂ (mask (E := E) P f x) (h x)
  apply tsum_congr
  intro x
  classical
  simp only [mask_apply]
  split_ifs <;> simp



end Mask

section Regular
variable {G : Type*} [Group G]
abbrev leftRegular (g : G) : VectorHilbert G E →L[ℂ] VectorHilbert G E :=
  MatrixRegularRestriction.leftRegular g
@[simp] theorem leftRegular_apply (g : G) (f : VectorHilbert G E) (h : G) :
    leftRegular g f h = f (g⁻¹ * h) := rfl
 theorem leftRegular_preserves_norm (g : G) (f : VectorHilbert G E) :
    ‖leftRegular g f‖ = ‖f‖ :=
  (RegularCoefficientEnergy.reindexIsometry (E := E) (Equiv.mulLeft g⁻¹)).norm_map f
 theorem leftRegular_mul (g h : G) :
    leftRegular (E := E) (g*h) = (leftRegular g).comp (leftRegular h) := by
  ext f x
  simp [mul_assoc]
end Regular
section Operators

variable {α : Type*} [DecidableEq α]

theorem leftRegular_adjoint {G : Type*} [Group G] (g : G) :
    (leftRegular (E := E) g).adjoint = leftRegular (E := E) g⁻¹ := by
  unfold leftRegular MatrixRegularRestriction.leftRegular
  change ((RegularCoefficientEnergy.reindexIsometry (E := E) (Equiv.mulLeft g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap).adjoint = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  change f ((Equiv.mulLeft g⁻¹).symm x) = f ((g⁻¹)⁻¹ * x)
  simp

theorem leftRegular_inner {G : Type*} [Group G] (g : G) (f h : VectorHilbert G E) :
    inner ℂ (leftRegular (E := E) g f) (leftRegular (E := E) g h) = inner ℂ f h :=
  (RegularCoefficientEnergy.reindexIsometry (Equiv.mulLeft g⁻¹)).inner_map_map f h

/-- A letter creation shift, retaining only words where the new letter does
not cancel. Its range consists of words with that reduced first letter. -/
def creation (s : Letter α) : VectorHilbert (FreeGroup α) E →L[ℂ] VectorHilbert (FreeGroup α) E :=
  (mask (E := E) (Cone s)).comp (leftRegular (E := E) (letter s))

@[simp] theorem creation_apply (s : Letter α) (f : VectorHilbert (FreeGroup α) E)
    (x : FreeGroup α) :
    creation (E := E) s f x = if Cone s x then f ((letter s)⁻¹ * x) else 0 := rfl

/-- Creation is equally the full shift restricted to its noncancelling input cone. -/
theorem creation_domain (s : Letter α) :
    creation (E := E) s = (leftRegular (E := E) (letter s)).comp (mask (E := E) (fun x => ¬ Cone (flip s) x)) := by
  ext f x
  have hc : Cone s x ↔ ¬ Cone (flip s) ((letter s)⁻¹ * x) := by
    simpa [mul_assoc] using cone_shift_iff s ((letter s)⁻¹ * x)
  simp [creation_apply, ContinuousLinearMap.comp_apply, mask_apply, hc]

theorem creation_adjoint (s : Letter α) :
    (creation (E := E) s).adjoint = (leftRegular (E := E) (letter s)⁻¹).comp (mask (E := E) (Cone s)) := by
  rw [creation, ContinuousLinearMap.adjoint_comp, mask_adjoint, leftRegular_adjoint]

/-- The actual regular generator is the sum of creation and inverse annihilation. -/
theorem leftRegular_letter_decomposition (s : Letter α) :
    leftRegular (E := E) (letter s) = creation (E := E) s + (creation (E := E) (flip s)).adjoint := by
  rw [creation_domain, creation_adjoint, letter_flip, inv_inv]
  ext f x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    lp.coeFn_add, Pi.add_apply, leftRegular_apply, mask_apply]
  by_cases hx : Cone (flip s) ((letter s)⁻¹ * x) <;> simp [hx]

theorem creation_norm_le (s : Letter α) (f : VectorHilbert (FreeGroup α) E) :
    ‖creation (E := E) s f‖ ≤ ‖f‖ :=
  (mask_norm_le (Cone s) (leftRegular (E := E) (letter s) f)).trans_eq
    (leftRegular_preserves_norm (letter s) f)

/-- Different first-letter creation ranges are orthogonal. -/
theorem creation_inner_zero {s t : Letter α} (hne : s ≠ t)
    (f h : VectorHilbert (FreeGroup α) E) : inner ℂ (creation (E := E) s f) (creation (E := E) t h) = 0 := by
  change (∑' x, inner ℂ (creation (E := E) s f x) (creation (E := E) t h x)) = 0
  have hz : ∀ x, inner ℂ (creation (E := E) s f x) (creation (E := E) t h x) = 0 := by
    intro x
    by_cases hs : Cone s x
    · have ht : ¬ Cone t x := fun ht => cone_disjoint hne x ⟨hs,ht⟩
      simp [creation_apply, ht]
    · simp [creation_apply, hs]
  simp_rw [hz]
  exact tsum_zero

/-- The middle cancellation term vanishes for different letters. -/
theorem creation_adjoint_comp_zero {s t : Letter α} (hne : s ≠ t) :
    (creation (E := E) s).adjoint.comp (creation (E := E) t) = 0 := by
  rw [creation_adjoint]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply,
    creation_apply, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hs : Cone s (letter s * x)
  · have ht : ¬ Cone t (letter s * x) := fun ht => cone_disjoint hne _ ⟨hs,ht⟩
    simp [hs, ht]
  · simp [hs]

/-- On another first-letter range, creation has no cancellation and is a full isometry. -/
theorem creation_comp_creation_eq_shift {s t : Letter α} (hne : flip s ≠ t) :
    (creation (E := E) s).comp (creation (E := E) t) = (leftRegular (E := E) (letter s)).comp (creation (E := E) t) := by
  rw [creation_domain]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply, creation_apply]
  by_cases hs : Cone (flip s) ((letter s)⁻¹ * x)
  · have ht : ¬ Cone t ((letter s)⁻¹ * x) := fun ht => cone_disjoint hne _ ⟨hs,ht⟩
    simp [hs, ht]
  · simp [hs]

/-- A reduced length-two shift has exactly three cancellation components. -/
theorem length_two_decomposition {s t : Letter α} (hne : flip s ≠ t) :
    leftRegular (E := E) (letter s * letter t) =
      (creation (E := E) s).comp (creation (E := E) t) +
      (creation (E := E) s).comp (creation (E := E) (flip t)).adjoint +
      (creation (E := E) (flip s)).adjoint.comp (creation (E := E) (flip t)).adjoint := by
  rw [leftRegular_mul, leftRegular_letter_decomposition s,
    leftRegular_letter_decomposition t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add, creation_adjoint_comp_zero hne, zero_add]

end Operators

section ConeEstimates

variable {α I : Type*} [DecidableEq α] [Fintype I]

theorem mask_cone_inner_zero {s t : Letter α} (hne : s ≠ t)
    (f h : VectorHilbert (FreeGroup α) E) :
    inner ℂ (mask (E := E) (Cone s) f) (mask (E := E) (Cone t) h) = 0 := by
  change (∑' x, inner ℂ (mask (E := E) (Cone s) f x) (mask (E := E) (Cone t) h x)) = 0
  have hz : ∀ x, inner ℂ (mask (E := E) (Cone s) f x) (mask (E := E) (Cone t) h x) = 0 := by
    intro x
    by_cases hs : Cone s x
    · have ht : ¬ Cone t x := fun ht => cone_disjoint hne x ⟨hs,ht⟩
      simp [mask_apply, ht]
    · simp [mask_apply, hs]
  simp_rw [hz]
  exact tsum_zero

theorem sum_cone_masks_eq (L : I → Letter α) (hL : Function.Injective L)
    (f : VectorHilbert (FreeGroup α) E) :
    (∑ i, mask (E := E) (Cone (L i)) f) = mask (E := E) (fun x => ∃ i, Cone (L i) x) f := by
  classical
  ext x
  simp only [lp.coeFn_sum, Finset.sum_apply, mask_apply]
  by_cases hx : ∃ i, Cone (L i) x
  · obtain ⟨i,hi⟩ := hx
    rw [if_pos ⟨i,hi⟩]
    have hz : ∀ j ≠ i, ¬ Cone (L j) x := by
      intro j hji hj
      exact cone_disjoint (fun he => hji (hL he)) x ⟨hj,hi⟩
    calc
      (∑ j, if Cone (L j) x then f x else 0) =
          (if Cone (L i) x then f x else 0) :=
        Finset.sum_eq_single i (fun j _ hji => by simp [hz j hji]) (by simp)
      _ = f x := by simp [hi]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ Cone (L i) x := fun hi => hx ⟨i,hi⟩
    simp [hi]

/-- The energies of disjoint concrete first-letter projections are bounded
by the total Hilbert-space energy. -/
theorem sum_cone_mask_norm_sq_le (L : I → Letter α) (hL : Function.Injective L)
    (f : VectorHilbert (FreeGroup α) E) :
    (∑ i, ‖mask (E := E) (Cone (L i)) f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have hsum := norm_sum_sq_of_inner_zero (fun i => mask (E := E) (Cone (L i)) f)
    (fun i j hij => mask_cone_inner_zero (fun he => hij (hL he)) f f)
  rw [sum_cone_masks_eq L hL f] at hsum
  have hn := mask_norm_le (fun x => ∃ i, Cone (L i) x) f
  nlinarith [norm_nonneg (mask (E := E) (fun x => ∃ i, Cone (L i) x) f), norm_nonneg f]

/-- The corresponding annihilation operators satisfy the same row-energy bound. -/
theorem sum_annihilation_norm_sq_le (L : I → Letter α) (hL : Function.Injective L)
    (f : VectorHilbert (FreeGroup α) E) :
    (∑ i, ‖(creation (E := E) (L i)).adjoint f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  simp_rw [creation_adjoint, ContinuousLinearMap.comp_apply, leftRegular_preserves_norm]
  exact sum_cone_mask_norm_sq_le L hL f

end ConeEstimates

section LengthTwo

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem creation_comp_flip_zero (s : Letter α) :
    (creation (E := E) s).comp (creation (E := E) (flip s)) = 0 := by
  rw [creation_domain]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply,
    creation_apply, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hx : Cone (flip s) ((letter s)⁻¹ * x) <;> simp [hx]

def doubleCreation (i j : α) :
    VectorHilbert (FreeGroup α) E →L[ℂ] VectorHilbert (FreeGroup α) E :=
  (creation (E := E) (i,false)).comp (creation (E := E) (j,true))

omit [Fintype α] in
@[simp] theorem doubleCreation_self (i : α) : doubleCreation (E := E) i i = 0 := by
  simpa [doubleCreation, FreeCreation.flip] using creation_comp_flip_zero (E := E) (i,false)

omit [Fintype α] in
theorem doubleCreation_norm_le (i j : α) (f : VectorHilbert (FreeGroup α) E) :
    ‖doubleCreation (E := E) i j f‖ ≤ ‖f‖ :=
  (creation_norm_le (i,false) (creation (E := E) (j,true) f)).trans (creation_norm_le (j,true) f)

omit [Fintype α] in
/-- Distinct reduced two-letter creation ranges are orthogonal. -/
theorem doubleCreation_inner_zero (p q : α × α) (hpq : p ≠ q)
    (f h : VectorHilbert (FreeGroup α) E) :
    inner ℂ (doubleCreation (E := E) p.1 p.2 f) (doubleCreation (E := E) q.1 q.2 h) = 0 := by
  by_cases hp : p.1 = p.2
  · simp [hp]
  by_cases hq : q.1 = q.2
  · simp [hq]
  by_cases hf : p.1 = q.1
  · have hs : p.2 ≠ q.2 := fun hs => hpq (Prod.ext hf hs)
    have hcp := creation_comp_creation_eq_shift (E := E)
      (s := (p.1,false)) (t := (p.2,true)) (by simpa [FreeCreation.flip] using hp)
    have hcq := creation_comp_creation_eq_shift (E := E)
      (s := (q.1,false)) (t := (q.2,true)) (by simpa [FreeCreation.flip] using hq)
    unfold doubleCreation
    rw [hcp, hcq]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hf, leftRegular_inner]
    exact creation_inner_zero (by simpa using hs) f h
  · exact creation_inner_zero (by simpa using hf) _ _


end LengthTwo
section Coefficients
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Pointwise coefficient operators commute with every coordinate creation. -/
theorem lift_creation_commute (B : E →L[ℂ] E) (s : Letter α) :
    (liftOperator B).comp (creation (E := E) s) = (creation (E := E) s).comp (liftOperator B) := by
  ext f x
  simp only [ContinuousLinearMap.comp_apply, RegularCoefficientEnergy.liftOperator_apply,
    creation_apply]
  split_ifs <;> simp



theorem lift_doubleCreation_commute (B : E →L[ℂ] E) (i j : α) :
    (liftOperator B).comp (doubleCreation (E := E) i j) =
      (doubleCreation (E := E) i j).comp (liftOperator B) := by
  rw [doubleCreation, ← ContinuousLinearMap.comp_assoc, lift_creation_commute,
    ContinuousLinearMap.comp_assoc, lift_creation_commute, ← ContinuousLinearMap.comp_assoc]

theorem lift_adjoint {G : Type*} (B : E →L[ℂ] E) :
    (liftOperator (G := G) B).adjoint = liftOperator B.adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (∑' x, inner ℂ (f x) (B (h x))) = ∑' x, inner ℂ (B.adjoint (f x)) (h x)
  apply tsum_congr
  intro x
  exact (ContinuousLinearMap.adjoint_inner_left B (h x) (f x)).symm

/-- The coefficient norm used in the operator-valued length-two estimate. -/
def coefficientLength (B : Matrix α α (E →L[ℂ] E)) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2)

theorem coefficientLength_sq (B : Matrix α α (E →L[ℂ] E)) :
    coefficientLength B ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 := Real.sq_sqrt (by positivity)

theorem coefficientLength_nonneg (B : Matrix α α (E →L[ℂ] E)) :
    0 ≤ coefficientLength B := Real.sqrt_nonneg _

/-- Orthogonal two-letter ranges control arbitrary operator coefficients. -/
theorem double_creation_sum_norm_le (B : Matrix α α (E →L[ℂ] E)) :
    ‖∑ i, ∑ j, (liftOperator (B i j)).comp (doubleCreation (E := E) i j)‖ ≤ coefficientLength B := by
  simp_rw [lift_doubleCreation_commute]
  apply ContinuousLinearMap.opNorm_le_bound _ (coefficientLength_nonneg B)
  intro f
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  have hsum := norm_sum_sq_of_inner_zero
    (fun p : α × α => doubleCreation (E := E) p.1 p.2 (liftOperator (B p.1 p.2) f))
    (fun p q hpq => doubleCreation_inner_zero p q hpq _ _)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hsum
  dsimp only at hsum
  have henergy : (∑ i, ∑ j, ‖doubleCreation (E := E) i j (liftOperator (B i j) f)‖ ^ 2) ≤
      (∑ i, ∑ j, ‖B i j‖ ^ 2) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hn := (doubleCreation_norm_le i j (liftOperator (B i j) f)).trans
      (RegularCoefficientEnergy.liftFunction_norm_le (B i j) f)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (coefficientLength_nonneg B) (norm_nonneg f))).mp
  rw [mul_pow, coefficientLength_sq, hsum]
  exact henergy

/-- The coefficient-valued one-cancellation component. -/
def mixed (B : Matrix α α (E →L[ℂ] E)) :
    VectorHilbert (FreeGroup α) E →L[ℂ] VectorHilbert (FreeGroup α) E :=
  ∑ i, ∑ j, (liftOperator (B i j)).comp
    ((creation (E := E) (i,false)).comp (creation (E := E) (j,false)).adjoint)

theorem mixed_norm_le (B : Matrix α α (E →L[ℂ] E)) : ‖mixed B‖ ≤ coefficientLength B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (coefficientLength_nonneg B)
  intro f
  let row : α → VectorHilbert (FreeGroup α) E :=
    fun i => ∑ j, liftOperator (B i j) ((creation (E := E) (j,false)).adjoint f)
  have he : mixed B f = ∑ i, creation (E := E) (i,false) (row i) := by
    unfold mixed
    simp_rw [← ContinuousLinearMap.comp_assoc, lift_creation_commute,
      ContinuousLinearMap.comp_assoc]
    simp [row, map_sum]
  rw [he]
  have hsum := norm_sum_sq_of_inner_zero (fun i => creation (E := E) (i,false) (row i))
    (fun i j hij => creation_inner_zero (by simpa using hij) _ _)
  have hrowenergy : (∑ j, ‖(creation (E := E) (j,false)).adjoint f‖ ^ 2) ≤ ‖f‖ ^ 2 :=
    sum_annihilation_norm_sq_le (fun j : α => (j,false))
      (by intro i j he; exact congrArg Prod.fst he) f
  have hrow : ∀ i, ‖row i‖ ^ 2 ≤ (∑ j, ‖B i j‖ ^ 2) * ‖f‖ ^ 2 := by
    intro i
    have hn : ‖row i‖ ≤ ∑ j, ‖B i j‖ * ‖(creation (E := E) (j,false)).adjoint f‖ := by
      change ‖∑ j, liftOperator (B i j) ((creation (E := E) (j,false)).adjoint f)‖ ≤ _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact RegularCoefficientEnergy.liftFunction_norm_le (G := FreeGroup α)
        (B i j) ((creation (E := E) (j,false)).adjoint f)
    have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => ‖B i j‖) (fun j => ‖(creation (E := E) (j,false)).adjoint f‖)
    have hp : ‖row i‖ ^ 2 ≤
        (∑ j, ‖B i j‖ ^ 2) * ∑ j, ‖(creation (E := E) (j,false)).adjoint f‖ ^ 2 := by
      nlinarith [norm_nonneg (row i)]
    exact hp.trans (mul_le_mul_of_nonneg_left hrowenergy (by positivity))
  have henergy : (∑ i, ‖creation (E := E) (i,false) (row i)‖ ^ 2) ≤
      (∑ i, ∑ j, ‖B i j‖ ^ 2) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hn := creation_norm_le (i,false) (row i)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hrow i)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (coefficientLength_nonneg B) (norm_nonneg f))).mp
  rw [mul_pow, coefficientLength_sq, hsum]
  exact henergy

def doubleAnnihilation (i j : α) :
    VectorHilbert (FreeGroup α) E →L[ℂ] VectorHilbert (FreeGroup α) E :=
  (doubleCreation (E := E) j i).adjoint

theorem doubleAnnihilation_eq (i j : α) :
    doubleAnnihilation (E := E) i j =
      (creation (E := E) (i,true)).adjoint.comp (creation (E := E) (j,false)).adjoint := by
  rw [doubleAnnihilation, doubleCreation, ContinuousLinearMap.adjoint_comp]



theorem double_annihilation_sum_norm_le (B : Matrix α α (E →L[ℂ] E)) :
    ‖∑ i, ∑ j, (liftOperator (B i j)).comp (doubleAnnihilation (E := E) i j)‖ ≤ coefficientLength B := by
  have hadj :
      ‖∑ i, ∑ j, (liftOperator (B i j)).comp (doubleAnnihilation (E := E) i j)‖ =
        ‖∑ i, ∑ j, (liftOperator (B i j).adjoint).comp (doubleCreation (E := E) j i)‖ := by
    rw [← (ContinuousLinearMap.adjoint.norm_map
      (∑ i, ∑ j, (liftOperator (B i j)).comp (doubleAnnihilation (E := E) i j)))]
    congr 1
    simp only [doubleAnnihilation, map_sum, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, lift_adjoint, lift_doubleCreation_commute]
  rw [hadj, Finset.sum_comm]
  have hbound := double_creation_sum_norm_le (fun i j => (B j i).adjoint)
  have he : coefficientLength (fun i j => (B j i).adjoint) = coefficientLength B := by
    unfold coefficientLength
    simp only [ContinuousLinearMap.adjoint.norm_map]
    rw [Finset.sum_comm]
  exact hbound.trans_eq he

/-- The actual operator-valued local regular polynomial. -/
def localPolynomial (B : Matrix α α (E →L[ℂ] E)) :
    VectorHilbert (FreeGroup α) E →L[ℂ] VectorHilbert (FreeGroup α) E :=
  ∑ i, ∑ j, (liftOperator (B i j)).comp
    (leftRegular (E := E) ((FreeGroup.of i)⁻¹ * FreeGroup.of j))

@[simp] theorem localPolynomial_apply (B : Matrix α α (E →L[ℂ] E))
    (f : VectorHilbert (FreeGroup α) E) (x : FreeGroup α) :
    localPolynomial B f x = ∑ i, ∑ j, B i j (f (((FreeGroup.of i)⁻¹ * FreeGroup.of j)⁻¹ * x)) := by
  simp [localPolynomial, RegularCoefficientEnergy.liftOperator_apply]

theorem local_polynomial_three_components (B : Matrix α α (E →L[ℂ] E))
    (hdiag : ∀ i, B i i = 0) :
    localPolynomial B = (∑ i, ∑ j, (liftOperator (B i j)).comp (doubleCreation (E := E) i j)) + mixed B +
      ∑ i, ∑ j, (liftOperator (B i j)).comp (doubleAnnihilation (E := E) i j) := by
  have hzero : (liftOperator (G := FreeGroup α) (0 : E →L[ℂ] E)) = 0 := by ext f x; simp
  have he : ∀ i j, (liftOperator (B i j)).comp (leftRegular (E := E) ((FreeGroup.of i)⁻¹ * FreeGroup.of j)) =
      (liftOperator (B i j)).comp (doubleCreation (E := E) i j) +
        (liftOperator (B i j)).comp ((creation (E := E) (i,false)).comp (creation (E := E) (j,false)).adjoint) +
        (liftOperator (B i j)).comp (doubleAnnihilation (E := E) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hdiag, hzero]
    · have hl := length_two_decomposition (E := E) (s := (i,false)) (t := (j,true))
        (by simpa [FreeCreation.flip] using hij)
      simp [letter, FreeCreation.flip] at hl
      rw [hl, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add, doubleAnnihilation_eq]
      rfl
  unfold localPolynomial mixed
  simp_rw [he]
  simp only [Finset.sum_add_distrib]

/-- Operator-valued length-two Haagerup bound, proved on the actual vector-valued
regular Hilbert space, with no operator norm input assumption. -/
theorem local_polynomial_norm_le_three_coeff (B : Matrix α α (E →L[ℂ] E))
    (hdiag : ∀ i, B i i = 0) :
    ‖localPolynomial B‖ ≤ 3 * Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  rw [local_polynomial_three_components B hdiag]
  have hfirst := double_creation_sum_norm_le B
  have hmiddle := mixed_norm_le B
  have hlast := double_annihilation_sum_norm_le B
  have hn1 := norm_add_le
    (∑ i, ∑ j, (liftOperator (B i j)).comp (doubleCreation (E := E) i j)) (mixed B)
  have hn2 := norm_add_le
    ((∑ i, ∑ j, (liftOperator (B i j)).comp (doubleCreation (E := E) i j)) + mixed B)
    (∑ i, ∑ j, (liftOperator (B i j)).comp (doubleAnnihilation (E := E) i j))
  change _ ≤ 3 * coefficientLength B
  linarith

end Coefficients

end Nonadditivity.CollinsYounTensor


