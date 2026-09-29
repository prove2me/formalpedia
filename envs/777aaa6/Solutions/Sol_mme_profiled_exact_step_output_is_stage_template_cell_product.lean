-- Prove2me | solution 1 for mme_profiled_exact_step_output_is_stage_template_cell_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T02:20:24.529988+00:00
-- url     : https://prove2.me/submissions/f6532817-f0d9-4204-8ce5-782f7ff2767b

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_recursive_yz_stage_certificate
import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction

open MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.ProfiledCW MME.CompleteSplit
open scoped Classical
universe u
set_option autoImplicit false

/-- The profiled-CW all-mode projection cut out by a cell/shape/usefulness filter is
literally the unbroken cell tensor, once the flat word length is transported along
`L * 2 ^ (ell - 1) = N`.  Both sides are `basisAllAllowedSubtensor` of the same
`(CWObj K 5).kronPow ·` along the same `kronPowModeWordBasis`, and after `subst` the
`Fin.cast` inside `ProfiledCW.split` becomes the identity, so the two predicates
coincide definitionally. -/
private theorem tensor_eq_unbroken {K : Type u} [Field K] {Pt C : Type} [Fintype Pt]
    (ell L N : ℕ) (h : L * 2 ^ (ell - 1) = N) (positions : Fin L ≃ Pt)
    (cell : Pt → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    ProfiledCW.tensor K
        (fun i y ↦ (∀ p, grade (ProfiledCW.split positions h y p) = shape (cell p) i) ∧
          Useful cell (mu i) (ProfiledCW.split positions h y))
      = unbroken K 5 ell L positions cell shape mu := by
  subst h
  rfl

/-- The output projection of an exact profiled-CW step is exactly the stage template:
`Graded` with shape `fun c i ↦ (c.2.val i).val` is the first clause of `CWCells.allowed`,
and `ProfiledCW.split … E.length` is `CWCells.label` after transporting the word length. -/
theorem exact_step_output_tensor_eq_template {K : Type u} [Field K] {ell N : ℕ}
    {P : ProfiledCW.Predicate N} (E : ProfiledCW.ExactStep ell N P) :
    ProfiledCW.tensor K E.output = E.stage.template K :=
  tensor_eq_unbroken E.stage.ell E.stage.L N E.length E.stage.positions
    (fullCell E.stage.total E.stage.reference) (fun c i ↦ (c.2.val i).val) E.stage.mu

theorem solution {K : Type u} [Field K] {ell N : ℕ} {P : ProfiledCW.Predicate N}
    (E : ProfiledCW.ExactStep ell N P)
    (D : Partition (fullCell E.stage.total E.stage.reference)) :
    ProfiledCW.tensor K E.output = E.stage.template K ∧
    Restrict
      (kronFin D.parts (D.piece K 5 E.stage.ell (fun c i ↦ (c.2.val i).val) E.stage.mu))
      (ProfiledCW.tensor K E.output) := by
  refine ⟨exact_step_output_tensor_eq_template E, ?_⟩
  rw [exact_step_output_tensor_eq_template (K := K) E]
  exact mme_recursive_yz_actual_cell_product_restriction 5 E.stage.ell E.stage.L
    E.stage.positions (fullCell E.stage.total E.stage.reference)
    (fun c i ↦ (c.2.val i).val) E.stage.mu D
