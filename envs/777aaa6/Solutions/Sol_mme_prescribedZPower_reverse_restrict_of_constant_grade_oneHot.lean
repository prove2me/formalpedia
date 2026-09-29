-- Prove2me | solution 1 for mme_prescribedZPower_reverse_restrict_of_constant_grade_oneHot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T07:50:19.380907+00:00
-- url     : https://prove2.me/submissions/4ae18047-88a2-4ec0-910f-cda5e218f664

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Convert

/-!
# Constant-grade one-hot prescribed-Z powers are the full powers

When every distinguished basis vector has the same grade and the prescribed
integer profile is supported wholly on that grade, every power word satisfies
the prescribed histogram.  The Z-only projection is therefore vacuous.  This
file proves the missing reverse restriction; the public projection theorem
already supplies the forward direction.
-/

set_option autoImplicit false
set_option warningAsError true

universe u

open PiTensorProduct DirectSum Module

namespace MME.PrescribedZConstantGradeOneHot

open MME
open DWZRestrictedValue DWZComponentRestriction

private theorem blockProj_subtype_of_class_eq_top
    {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (sigma : Fin d → Fin t)
    (htop : ∀ i, G.classOf i (sigma i) = ⊤) (i : Fin d) :
    (G.classOf i (sigma i)).subtype.comp (G.blockProj i (sigma i)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ G.decomp i (sigma i) := by
    rw [show G.decomp i (sigma i) = ⊤ from htop i]
    exact Submodule.mem_top
  have hcomponent :=
    (G.is_internal i).ofBijective_coeLinearMap_of_mem hx
  change ((G.modeLequiv i).symm x) (sigma i) = ⟨x, hx⟩ at hcomponent
  exact congrArg Subtype.val hcomponent

private theorem blockSubtensor_reverse_of_classes_eq_top
    {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (sigma : Fin d → Fin t)
    (htop : ∀ i, G.classOf i (sigma i) = ⊤) :
    TensorObj.Restrict T (G.blockSubtensor sigma) := by
  refine ⟨fun i => (G.classOf i (sigma i)).subtype, ?_⟩
  change PiTensorProduct.map
      (fun i => (G.classOf i (sigma i)).subtype)
      (PiTensorProduct.map (fun i => G.blockProj i (sigma i)) T.t) = T.t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hmaps :
      (fun i => (G.classOf i (sigma i)).subtype.comp
        (G.blockProj i (sigma i))) =
      (fun _ => LinearMap.id) := by
    funext i
    exact blockProj_subtype_of_class_eq_top G sigma htop i
  rw [hmaps, PiTensorProduct.map_id]
  rfl

private theorem basisZAllowedSubtensor_reverse_of_forall
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} (bZ : Basis ι K (T.V 2))
    (allowed : ι → Prop) [DecidablePred allowed]
    (hall : ∀ j, allowed j) :
    TensorObj.Restrict T (T.basisZAllowedSubtensor bZ allowed) := by
  rcases mme_basisZAllowedSubtensor_projection_certificate T bZ allowed with
    ⟨_, h0, h1, h2⟩
  apply blockSubtensor_reverse_of_classes_eq_top
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · change (T.basisZAllowedGrading bZ allowed).classOf 2 0 = ⊤
    rw [h2]
    convert bZ.span_eq
    ext x
    simp [hall]

private theorem prescribedZWord_of_constant_grade_oneHot
    {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a, p.count a = if a = a0 then p.denominator else 0)
    (m : ℕ) (w : PowIndex ι (p.length m)) :
    prescribedZWord grade p m w := by
  intro a
  by_cases ha : a = a0
  · subst a
    have hfilter :
        Finset.univ.filter
          (fun r : Fin (p.length m) =>
            grade (PowIndex.get (p.length m) w r) = a0) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro r _
      exact hgrade _
    rw [leftGradeCount, hfilter, Finset.card_univ, Fintype.card_fin]
    simp [hone, IntegerZSplitProfile.length]
  · have hfilter :
        Finset.univ.filter
          (fun r : Fin (p.length m) =>
            grade (PowIndex.get (p.length m) w r) = a) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r _ har
      apply ha
      calc
        a = grade (PowIndex.get (p.length m) w r) := har.symm
        _ = a0 := hgrade _
    rw [leftGradeCount, hfilter]
    simp [hone, ha]

/-- A constant basis grade and the corresponding one-hot integer profile make
the prescribed-Z projection vacuous, in the previously missing reverse
restriction direction. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a, p.count a = if a = a0 then p.denominator else 0)
    (m : ℕ) :
    TensorObj.Restrict (T.kronPow (p.length m))
      (prescribedZPower T bZ grade p m) := by
  classical
  rw [prescribedZPower]
  apply basisZAllowedSubtensor_reverse_of_forall
  intro w
  exact prescribedZWord_of_constant_grade_oneHot grade p a0 hgrade hone m w

/-- The defining Z projection always restricts to its ambient tensor power. -/
theorem prescribedZPower_restrict_kronPow
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (m : ℕ) :
    TensorObj.Restrict (prescribedZPower T bZ grade p m)
      (T.kronPow (p.length m)) := by
  classical
  rw [prescribedZPower]
  exact (mme_basisZAllowedSubtensor_projection_certificate
    (T.kronPow (p.length m))
    (kronPowModeBasis T 2 bZ (p.length m))
    (prescribedZWord grade p m)).1

/-- Hence a constant-grade one-hot prescribed power is tensor-isomorphic to
the full ambient power, independently of which basis of the actual Z-space
was chosen. -/
theorem isomorphic_kronPow_of_constant_grade_oneHot
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a, p.count a =
      if a = a0 then p.denominator else 0)
    (m : ℕ) :
    TensorObj.Isomorphic (prescribedZPower T bZ grade p m)
      (T.kronPow (p.length m)) := by
  exact ⟨prescribedZPower_restrict_kronPow T bZ grade p m,
    solution T bZ grade p a0 hgrade hone m⟩

end MME.PrescribedZConstantGradeOneHot


open MME MME.DWZRestrictedValue

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a, p.count a = if a = a0 then p.denominator else 0)
    (m : ℕ) :
    TensorObj.Restrict (T.kronPow (p.length m))
      (prescribedZPower T bZ grade p m) := by
  exact MME.PrescribedZConstantGradeOneHot.solution
    T bZ grade p a0 hgrade hone m
