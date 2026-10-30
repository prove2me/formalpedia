-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.ParamClass.bgf_binaryWords_closed
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:46.186803+00:00
-- url     : https://prove2.me/submissions/a96c12a2-d424-4b9c-b6ab-9337ccceb926

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_BinaryWords
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch3 -- Binary words marked by number of ones

The class of binary words of length `n`, with the bivariate parameter counting
the number of ones, has BGF `1 / (1 - (1 + u) z)`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

private lemma sum_pow_card_finset (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ s : Finset α, (Polynomial.X : ℚ[X]) ^ s.card) =
      (1 + Polynomial.X : ℚ[X]) ^ Fintype.card α := by
  simpa [Finset.prod_eq_pow_card] using
    (Finset.prod_one_add (s := (Finset.univ : Finset α))
      (f := fun _ : α => (Polynomial.X : ℚ[X]))).symm

/-- The size-`n` parameter polynomial for binary words is `(1 + u)^n`. -/
lemma paramPoly_binaryWords (n : ℕ) :
    ParamClass.binaryWords.paramPoly n = (1 + Polynomial.X : ℚ[X]) ^ n := by
  classical
  rw [ParamClass.paramPoly, ParamClass.binaryWords]
  change (∑ f : Fin n → Bool,
      (Polynomial.X : ℚ[X]) ^
        (Finset.univ.filter (fun i => f i = true)).card) =
    (1 + Polynomial.X : ℚ[X]) ^ n
  let e : (Fin n → Bool) ≃ Finset (Fin n) := binaryWordsEquivFinset n
  calc
    (∑ f : Fin n → Bool,
        (Polynomial.X : ℚ[X]) ^
          (Finset.univ.filter (fun i => f i = true)).card)
        = ∑ s : Finset (Fin n),
            (Polynomial.X : ℚ[X]) ^
              (Finset.univ.filter (fun i => e.symm s i = true)).card := by
          simpa using
            (Equiv.sum_comp e.symm
              (fun f : Fin n → Bool =>
                (Polynomial.X : ℚ[X]) ^
                  (Finset.univ.filter (fun i => f i = true)).card)).symm
    _ = ∑ s : Finset (Fin n), (Polynomial.X : ℚ[X]) ^ s.card := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have hset :
              (Finset.univ.filter (fun i => e.symm s i = true)) = s := by
            ext i
            simp [e, binaryWordsEquivFinset]
          rw [hset]
    _ = (1 + Polynomial.X : ℚ[X]) ^ n := by
          rw [sum_pow_card_finset, Fintype.card_fin]

private lemma coeff_mul_C_mul_X (F : ℚ[X]⟦X⟧) (A : ℚ[X]) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * (PowerSeries.C A * PowerSeries.X)) =
      PowerSeries.coeff n F * A := by
  rw [show F * (PowerSeries.C A * PowerSeries.X) =
      (F * PowerSeries.C A) * PowerSeries.X by
        set_option backward.isDefEq.respectTransparency false in
          ring]
  rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open scoped Polynomial
open PowerSeries Finset
theorem solution :
    ParamClass.binaryWords.bgf *
        (1 - PowerSeries.C (1 + Polynomial.X : ℚ[X]) *
          (PowerSeries.X : ℚ[X]⟦X⟧)) =
      1 := by
  classical
  let F : ℚ[X]⟦X⟧ := ParamClass.binaryWords.bgf
  let A : ℚ[X] := 1 + Polynomial.X
  have hF : ∀ n : ℕ, PowerSeries.coeff n F = A ^ n := by
    intro n
    simp [F, A, ParamClass.bgf, paramPoly_binaryWords]
  have hmain : F * (1 - PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) = 1 := by
    have expand : F * (1 - PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) =
        F - F * (PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) := by
      set_option backward.isDefEq.respectTransparency false in
        ring
    rw [expand]
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · rw [map_sub, hF 0]
      simp
    · rw [map_sub, hF (n + 1), coeff_mul_C_mul_X F A n, hF n]
      simp
      rw [pow_succ']
      ring
  simpa [F, A] using hmain
