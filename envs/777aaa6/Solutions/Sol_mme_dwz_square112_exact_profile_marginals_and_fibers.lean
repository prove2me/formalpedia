-- Prove2me | solution 1 for mme_dwz_square112_exact_profile_marginals_and_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:22:22.442123+00:00
-- url     : https://prove2.me/submissions/05ac1b38-80fe-4b2d-a55a-534294bdc544

import Definitions.Def_mme_dwz_square112_exact_profile_data
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

open MME.DWZSquare112
open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem marginal_eq_fiber_sum (c : Fin 4 → ℕ) (i a : Fin 3) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin 4 ↦ row r i = a), c r) =
      marginal c i a := by
  have hsets : (fun i a : Fin 3 ↦
      Finset.univ.filter (fun r : Fin 4 ↦ row r i = a)) =
      ![![{0, 1}, {2, 3}, ∅], ![{0, 2}, {1, 3}, ∅],
        ![{3}, {1, 2}, {0}]] := by decide
  rw [congrFun (congrFun hsets i) a]
  fin_cases i <;> fin_cases a
  · exact Finset.sum_pair (by decide)
  · exact Finset.sum_pair (by decide)
  · exact Finset.sum_empty
  · exact Finset.sum_pair (by decide)
  · exact Finset.sum_pair (by decide)
  · exact Finset.sum_empty
  · exact Finset.sum_singleton c 3
  · exact Finset.sum_pair (by decide)
  · exact Finset.sum_singleton c 0

private theorem exact_mode_card {N : ℕ} {c : Fin 4 → ℕ}
    (w : ExactWord N c) (i a : Fin 3) :
    Fintype.card {j : Fin N // modeWord w i j = a} = marginal c i a := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin N))
    (Finset.univ.filter (fun r : Fin 4 ↦ row r i = a)) w.1
  have hsum :
      ∑ r ∈ Finset.univ.filter (fun r : Fin 4 ↦ row r i = a),
        Fintype.card {j : Fin N // w.1 j = r} =
      Fintype.card {j : Fin N // modeWord w i j = a} := by
    simpa only [Fintype.card_subtype, Finset.mem_filter,
      Finset.mem_univ, true_and, modeWord] using hfiber
  rw [← hsum]
  simp_rw [w.2]
  exact marginal_eq_fiber_sum c i a

theorem solution (N : ℕ) (c : Fin 4 → ℕ) :
    (∀ (w : ExactWord N c) (i a : Fin 3),
      Fintype.card {j : Fin N // modeWord w i j = a} = marginal c i a) ∧
    ∀ (i : Fin 3) (x : Fin N → Fin 3),
      (∀ a : Fin 3, Fintype.card {j : Fin N // x j = a} = marginal c i a) →
      Nat.card {v : ExactWord N c // modeWord v i = x} =
        ∏ a : Fin 3,
          (marginal c i a).factorial /
            ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial := by
  classical
  refine ⟨fun w ↦ exact_mode_card w, ?_⟩
  intro i x hx
  let Assignment := {g : Fin N → Fin 4 //
    (∀ j, row (g j) i = x j) ∧
      ∀ r : Fin 4, Fintype.card {j : Fin N // g j = r} = c r}
  let e : {v : ExactWord N c // modeWord v i = x} ≃ Assignment := {
    toFun v := ⟨v.1.1, (fun j ↦ congrFun v.2 j), v.1.2⟩
    invFun g := ⟨⟨g.1, g.2.2⟩, funext g.2.1⟩
    left_inv v := by rfl
    right_inv g := by rfl
  }
  have hsum (a : Fin 3) :
      (∑ r : {r : Fin 4 // row r i = a}, c r.1) =
        Fintype.card {j : Fin N // x j = a} := by
    rw [hx a]
    rw [← marginal_eq_fiber_sum c i a]
    exact (Finset.sum_subtype
      (Finset.univ.filter (fun r : Fin 4 ↦ row r i = a))
      (fun r ↦ by simp) c).symm
  rw [Nat.card_congr e]
  change Nat.card Assignment = _
  have hcount := mme_fintype_constrained_prescribed_fiber_function_card
    x (fun r : Fin 4 ↦ row r i) c hsum
  simpa only [Assignment, hx] using hcount
