-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis_v2
-- name    : ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T13:19:11.107123+00:00
-- url     : https://prove2.me/theorems/44b604ef-ed6f-43d0-90be-08c1eb582370
-- title:
--   Unit-pivot basis of a relation module
-- statement:
--   Defines a system over a commutative ring with original indices $I$, retained indices $J$ mapped into $I$, linearly independent retained values, and finite reconstruction coefficients. Rows indexed by the omitted part of $I$ form a basis of the evaluation map’s relation module.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR8/UnitPivotBasis.lean#L35-L70
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR8/UnitPivotBasis.lean#L212-L235

import Mathlib
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-!
# Unit-pivot bases of relation modules

Round 8. New proof source; no local compiler was available.
All indices may be infinite: the source of evaluation is a `Finsupp`, not an
unrestricted product. In the finite application it is the ordinary free module
on all channels. The proof is valid over a commutative ring, in particular Z.

Pinned API source: mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
`Finsupp.linearCombination`, its single and composition rules, and
`Finsupp.mem_span_range_iff_exists_finsupp` are in
Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean.
`Finsupp.lhom_ext`, `Finsupp.lapply` are in
Mathlib/LinearAlgebra/Finsupp/Defs.lean.
`Module.Basis.span` and `Module.Basis.coe_span_apply` are in
Mathlib/LinearAlgebra/Basis/Basic.lean.
`Module.Basis.map` is in Mathlib/LinearAlgebra/Basis/Defs.lean.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot

open scoped BigOperators

variable {R I J M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Data for a generating family with an explicitly retained independent
subfamily. `coeff` is a finite normal form for each original channel. -/
structure System (R I J M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  value : I → M
  keep : J → I
  independent : LinearIndependent R (fun j => value (keep j))
  coeff : I → J →₀ R
  reconstruct : ∀ i,
    Finsupp.linearCombination R (fun j => value (keep j)) (coeff i) = value i

namespace System

variable (D : System R I J M)

/-- The actual free-module evaluation whose kernel is the relation module. -/
noncomputable def evaluation : (I →₀ R) →ₗ[R] M :=
  Finsupp.linearCombination R D.value

noncomputable def keptEvaluation : (J →₀ R) →ₗ[R] M :=
  Finsupp.linearCombination R (fun j => D.value (D.keep j))

noncomputable def normalCoordinates : (I →₀ R) →ₗ[R] (J →₀ R) :=
  Finsupp.linearCombination R D.coeff

noncomputable def includeKept : (J →₀ R) →ₗ[R] (I →₀ R) :=
  Finsupp.linearCombination R (fun j => Finsupp.single (D.keep j) 1)

/-- Only a non-retained coordinate is used as a pivot. -/
def Omitted := { i : I // i ∉ Set.range D.keep }

noncomputable def row (i : I) : I →₀ R :=
  Finsupp.single i 1 - D.includeKept (D.coeff i)

noncomputable def rows : D.Omitted → I →₀ R := fun i => D.row i.val

/-- The normal-form coefficients of a retained generator are its unit vector.
This uses independence, not a choice convention for `coeff`. -/
theorem coeff_keep (j : J) : D.coeff (D.keep j) = Finsupp.single j 1 := by
  apply D.independent
  calc
    Finsupp.linearCombination R (fun j => D.value (D.keep j))
        (D.coeff (D.keep j)) = D.value (D.keep j) := D.reconstruct _
    _ = Finsupp.linearCombination R (fun j => D.value (D.keep j))
        (Finsupp.single j 1) := by
          rw [Finsupp.linearCombination_single, one_smul]

theorem includeKept_single (j : J) (a : R) :
    D.includeKept (Finsupp.single j a) = Finsupp.single (D.keep j) a := by
  -- Mathlib/Data/Finsupp/SMul.lean: Finsupp.smul_single_one.
  rw [includeKept, Finsupp.linearCombination_single, Finsupp.smul_single_one]

theorem row_keep (j : J) : D.row (D.keep j) = 0 := by
  rw [row, D.coeff_keep, D.includeKept_single, sub_self]

/-- The evaluation of the kept inclusion is the independent evaluation. -/
theorem evaluation_includeKept (c : J →₀ R) :
    D.evaluation (D.includeKept c) = D.keptEvaluation c := by
  have hm : D.evaluation.comp D.includeKept = D.keptEvaluation := by
    apply Finsupp.lhom_ext
    intro j a
    rw [LinearMap.comp_apply, D.includeKept_single]
    change Finsupp.linearCombination R D.value (Finsupp.single (D.keep j) a) =
      Finsupp.linearCombination R (fun j => D.value (D.keep j)) (Finsupp.single j a)
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  exact LinearMap.congr_fun hm c

/-- Reconstructing the normal coordinates recovers the original evaluation. -/
theorem keptEvaluation_normalCoordinates (c : I →₀ R) :
    D.keptEvaluation (D.normalCoordinates c) = D.evaluation c := by
  have hm : D.keptEvaluation.comp D.normalCoordinates = D.evaluation := by
    apply Finsupp.lhom_ext
    intro i a
    rw [LinearMap.comp_apply]
    change D.keptEvaluation
        (Finsupp.linearCombination R D.coeff (Finsupp.single i a)) =
      Finsupp.linearCombination R D.value (Finsupp.single i a)
    rw [Finsupp.linearCombination_single, map_smul,
      Finsupp.linearCombination_single]
    change a • Finsupp.linearCombination R (fun j => D.value (D.keep j))
      (D.coeff i) = a • D.value i
    rw [D.reconstruct]
  exact LinearMap.congr_fun hm c

theorem normalCoordinates_eq_zero_of_relation (c : I →₀ R)
    (hc : D.evaluation c = 0) : D.normalCoordinates c = 0 := by
  apply D.independent
  change D.keptEvaluation (D.normalCoordinates c) = D.keptEvaluation 0
  rw [D.keptEvaluation_normalCoordinates, hc, map_zero]

theorem evaluation_row (i : I) : D.evaluation (D.row i) = 0 := by
  rw [row, map_sub, D.evaluation_includeKept]
  change Finsupp.linearCombination R D.value (Finsupp.single i 1) -
    Finsupp.linearCombination R (fun j => D.value (D.keep j)) (D.coeff i) = 0
  rw [Finsupp.linearCombination_single, one_smul, D.reconstruct, sub_self]

/-- A kept inclusion has no coefficient at an omitted index. -/
theorem includeKept_at_omitted (o : D.Omitted) (c : J →₀ R) :
    D.includeKept c o.val = 0 := by
  classical
  have hm :
      (Finsupp.lapply o.val : (I →₀ R) →ₗ[R] R).comp D.includeKept = 0 := by
    apply Finsupp.lhom_ext
    intro j a
    rw [LinearMap.comp_apply, D.includeKept_single, Finsupp.lapply_apply]
    have hne : D.keep j ≠ o.val := fun h => o.property ⟨j, h⟩
    -- Mathlib/Data/Finsupp/Single.lean: the primed rule takes centre != argument.
    simp only [Finsupp.single_eq_of_ne' hne, LinearMap.zero_apply]
  have h := LinearMap.congr_fun hm c
  change D.includeKept c o.val = 0 at h
  exact h

/-- Unit pivots survive subtraction of the retained normal form. -/
theorem row_at_omitted (i : I) (o : D.Omitted) :
    D.row i o.val = Finsupp.single i (1 : R) o.val := by
  change Finsupp.single i (1 : R) o.val - D.includeKept (D.coeff i) o.val = _
  rw [D.includeKept_at_omitted, sub_zero]

/-- Evaluating a combination of reduction rows at its omitted pivot recovers
that coefficient, even for an infinite family of channels. -/
theorem combination_at_pivot (c : D.Omitted →₀ R) (o : D.Omitted) :
    (Finsupp.linearCombination R D.rows c) o.val = c o := by
  classical
  have hm :
      (Finsupp.lapply o.val : (I →₀ R) →ₗ[R] R).comp
        (Finsupp.linearCombination R D.rows) =
      (Finsupp.lapply o : (D.Omitted →₀ R) →ₗ[R] R) := by
    apply Finsupp.lhom_ext
    intro j a
    rw [LinearMap.comp_apply, Finsupp.linearCombination_single,
      Finsupp.lapply_apply, Finsupp.lapply_apply]
    change a * D.row j.val o.val = Finsupp.single j a o
    rw [D.row_at_omitted]
    by_cases h : j = o
    · subst j
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same, mul_one]
    · have hv : j.val ≠ o.val := fun hv => h (Subtype.ext hv)
      rw [Finsupp.single_eq_of_ne' hv, Finsupp.single_eq_of_ne' h, mul_zero]
  exact LinearMap.congr_fun hm c

/-- Independence uses pivots of coefficient one and needs no division. -/
theorem rows_independent : LinearIndependent R D.rows := by
  intro c d h
  apply Finsupp.ext
  intro o
  have hp := congrArg (fun x : I →₀ R => x o.val) h
  change (Finsupp.linearCombination R D.rows c) o.val =
    (Finsupp.linearCombination R D.rows d) o.val at hp
  rw [D.combination_at_pivot, D.combination_at_pivot] at hp
  exact hp

/-- The elimination operator is the linear combination of elementary rows. -/
theorem subtraction_eq_rows (c : I →₀ R) :
    c - D.includeKept (D.normalCoordinates c) =
      Finsupp.linearCombination R D.row c := by
  have hm :
      (LinearMap.id - D.includeKept.comp D.normalCoordinates) =
        Finsupp.linearCombination R D.row := by
    apply Finsupp.lhom_ext
    intro i a
    change Finsupp.single i a -
      D.includeKept (Finsupp.linearCombination R D.coeff (Finsupp.single i a)) =
      Finsupp.linearCombination R D.row (Finsupp.single i a)
    rw [Finsupp.linearCombination_single, map_smul,
      Finsupp.linearCombination_single, row, smul_sub,
      Finsupp.smul_single_one]
  exact LinearMap.congr_fun hm c

/-- Every row, including a retained row (which is zero), belongs to the span
of the omitted-pivot rows. -/
theorem row_mem_span_rows (i : I) :
    D.row i ∈ Submodule.span R (Set.range D.rows) := by
  classical
  by_cases hi : i ∈ Set.range D.keep
  · obtain ⟨j, rfl⟩ := hi
    rw [D.row_keep]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

/-- Spanning of the *kernel*, not merely spanning of the image. -/
theorem span_rows_eq_ker :
    Submodule.span R (Set.range D.rows) = LinearMap.ker D.evaluation := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨o, rfl⟩
    exact D.evaluation_row o.val
  · intro c hc
    have hz : D.normalCoordinates c = 0 :=
      D.normalCoordinates_eq_zero_of_relation c hc
    have hnormal := D.subtraction_eq_rows c
    rw [hz, map_zero, sub_zero] at hnormal
    rw [hnormal]
    change c.sum (fun i a => a • D.row i) ∈ _
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (D.row_mem_span_rows i))

/-- The reduction rows form an actual module basis of the relation module. -/
noncomputable def relationBasis :
    Module.Basis D.Omitted R (LinearMap.ker D.evaluation) :=
  (Module.Basis.span D.rows_independent).map
    (LinearEquiv.ofEq _ _ D.span_rows_eq_ker)





end System

end ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot

namespace ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot.System

variable {R I J M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (D : System R I J M)

theorem keep_injective [Nontrivial R] : Function.Injective D.keep := by
  intro i j hij
  exact D.independent.injective (congrArg D.value hij)

noncomputable instance omittedFintype [Fintype I] : Fintype D.Omitted := by
  classical
  change Fintype {i : I // i ∉ Set.range D.keep}
  infer_instance

/-- The retained/omitted partition counts the pivots without a field argument. -/
noncomputable def indexSplit [Nontrivial R] : (J ⊕ D.Omitted) ≃ I := by
  classical
  let f : J ⊕ D.Omitted → I := Sum.elim D.keep Subtype.val
  have hinj : Function.Injective f := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (D.keep_injective h)
      | inr y => exact False.elim (y.property ⟨x, h⟩)
    | inr x =>
      cases y with
      | inl y => exact False.elim (x.property ⟨y, h.symm⟩)
      | inr y => exact congrArg Sum.inr (Subtype.ext h)
  have hsurj : Function.Surjective f := by
    intro i
    by_cases hi : i ∈ Set.range D.keep
    · obtain ⟨j, hj⟩ := hi
      exact ⟨Sum.inl j, hj⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩
  -- Mathlib/Logic/Equiv/Defs.lean: Equiv.ofBijective.
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩



end ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot.System


