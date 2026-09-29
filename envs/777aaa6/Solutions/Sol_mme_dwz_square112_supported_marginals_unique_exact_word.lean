-- Prove2me | solution 1 for mme_dwz_square112_supported_marginals_unique_exact_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:51:25.077859+00:00
-- url     : https://prove2.me/submissions/bfb7f75d-dd51-4475-87da-7698cac863fe

import Definitions.Def_mme_dwz_square112_exact_profile_data
import Theorems.Thm_mme_dwz_square112_exact_profile_marginals_and_fibers
import Mathlib.Tactic.FinCases

open MME.DWZSquare112

set_option autoImplicit false
set_option warningAsError true

private theorem row_injective : Function.Injective row := by decide

theorem solution
    (N : ℕ) (c : Fin 4 → ℕ) (x : Fin 3 → Fin N → Fin 3)
    (hsupport : ∀ j : Fin N, ∃ r : Fin 4, ∀ i : Fin 3, row r i = x i j)
    (hmarginal : ∀ i a : Fin 3,
      Fintype.card {j : Fin N // x i j = a} = marginal c i a) :
    ∃! w : ExactWord N c, modeWord w = x := by
  classical
  let decoded : Fin N → Fin 4 := fun j ↦ Classical.choose (hsupport j)
  have hdecoded (j : Fin N) (i : Fin 3) : row (decoded j) i = x i j :=
    Classical.choose_spec (hsupport j) i
  let actualCount : Fin 4 → ℕ := fun r ↦ Fintype.card {j : Fin N // decoded j = r}
  let actual : ExactWord N actualCount := ⟨decoded, fun _ ↦ rfl⟩
  have hactual : modeWord actual = x := by
    funext i j
    exact hdecoded j i
  have hmarginals (i a : Fin 3) : marginal actualCount i a = marginal c i a := by
    have h := (mme_dwz_square112_exact_profile_marginals_and_fibers N actualCount).1
      actual i a
    rw [hactual] at h
    exact h.symm.trans (hmarginal i a)
  have hcounts : actualCount = c := by
    have h0 := hmarginals 2 2
    have h3 := hmarginals 2 0
    have hX0 := hmarginals 0 0
    have hY0 := hmarginals 1 0
    change actualCount 0 = c 0 at h0
    change actualCount 3 = c 3 at h3
    change actualCount 0 + actualCount 1 = c 0 + c 1 at hX0
    change actualCount 0 + actualCount 2 = c 0 + c 2 at hY0
    rw [h0] at hX0 hY0
    funext r
    fin_cases r
    · exact h0
    · exact Nat.add_left_cancel hX0
    · exact Nat.add_left_cancel hY0
    · exact h3
  let w : ExactWord N c := ⟨decoded, fun r ↦ congrFun hcounts r⟩
  have hw : modeWord w = x := by
    funext i j
    exact hdecoded j i
  refine ⟨w, hw, ?_⟩
  intro v hv
  apply Subtype.ext
  funext j
  apply row_injective
  funext i
  change modeWord v i j = modeWord w i j
  rw [hv, hw]
