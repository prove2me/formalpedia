-- Prove2me | Theorems.Thm_mme_released_116_full_child_weight_assembly
-- name    : mme_released_116_full_child_weight_assembly
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:31:45.914389+00:00
-- url     : https://prove2.me/theorems/7480d304-950d-49ba-8a24-08dccfd1fba6
-- title:
--   Boundary and interior extraction weights assemble on the full released child tensor
-- statement:
--   There is an exact partition of the released 116 child index into eighteen boundary cells and six canonical 112 cells. Given a square matrix extraction from the six-fold symmetrized boundary product and a matrix-family extraction from the six-fold symmetrized interior product, this theorem extracts the dimension-scaled matrix family from the full six-fold symmetrized 24-child product in any enumeration. The interior summand count is preserved and the two exponential weight rates add. This is a conditional assembly theorem; the extraction hypotheses and their numerical rates must be supplied separately.
-- source:
--   Exact released child partition and square-times-family tensor extraction.

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_sixSymmetrization_restrict
open MME MME.RecursiveYZ MME.Released116
open MME BigOperators
set_option autoImplicit false
universe u

theorem mme_released_116_full_child_weight_assembly :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3) (q M : ℕ)
        (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ),
        TensorObj.Restrict (MMObj K M M M)
          (sixSymmetrization (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))) →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (sixSymmetrization (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
            change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
            decide⟩⟩))) →
        Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau →
        Real.exp interiorRate ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
          (sixSymmetrization (TensorObj.kronFin 24 (fun i ↦ T (d i)))) ∧
        Real.exp (boundaryRate + interiorRate) ≤
          ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by sorry
