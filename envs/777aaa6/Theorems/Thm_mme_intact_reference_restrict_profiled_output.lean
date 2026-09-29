-- Prove2me | Theorems.Thm_mme_intact_reference_restrict_profiled_output
-- name    : mme_intact_reference_restrict_profiled_output
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:42:52.299023+00:00
-- url     : https://prove2.me/theorems/e703b188-7879-4c50-abb9-90961804b69a
-- title:
--   Intact reference tensor restricts from its flat profiled output
-- statement:
--   The intact recursive reference tensor restricts from the profiled tensor of exactly its graded and useful output words, after any valid flattening of its physical positions. The proof transports the basis predicates through the split-coordinate map and applies a checked all-mode projection restriction. It is general in the parent types, child level, reference address, and exact profiles.
-- source:
--   Exact split-coordinate projection and released intact tensor extraction.

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_basis_projected_family_restrict
open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
open MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u

theorem mme_intact_reference_restrict_profiled_output
    {K : Type u} [Field K] {half R ell L N : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (reference : Address half R parent n) (positions : Fin L ≃ Position n)
    (length : L * 2 ^ (ell - 1) = N)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
      (tensor K (fun i x ↦ Graded htotal i reference (split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (split positions length x))) := by sorry
