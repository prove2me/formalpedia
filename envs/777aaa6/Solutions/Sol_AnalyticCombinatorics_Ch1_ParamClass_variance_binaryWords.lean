-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.ParamClass.variance_binaryWords
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:50.980201+00:00
-- url     : https://prove2.me/submissions/cc1e1169-d150-4ff5-94fc-0889769832a4

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_BinaryWords
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Variance
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Composition
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

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Moments of bivariate generating functions

The first factorial moment differentiates the parameter variable `u` and then
sets `u = 1`.  For a parameterized class this extracts the cumulative parameter
over each fixed-size fiber.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The first factorial moment coefficient is the cumulative parameter value on
the size-`n` fiber. -/
theorem ParamClass.coeff_factorialMoment1 (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (factorialMoment1 C.bgf) = ∑ x : C.Obj n, (C.param n x : ℚ) := by
  classical
  simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf, ParamClass.paramPoly,
    Polynomial.derivative_X_pow]

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Variance and bivariate composition facts

The second factorial moment differentiates twice in the parameter variable.
Adding the first factorial moment gives the second raw moment, hence the usual
variance formula for any parameterized class.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The second factorial moment coefficient is the cumulative `p(p-1)` on the
size-`n` fiber. -/
theorem ParamClass.coeff_factorialMoment2 (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (factorialMoment2 C.bgf) =
      ∑ x : C.Obj n, (C.param n x : ℚ) * ((C.param n x : ℚ) - 1) := by
  classical
  simp [factorialMoment2, evalU, uDeriv, ParamClass.bgf, ParamClass.paramPoly,
    Polynomial.derivative_X_pow]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : C.param n x = 0
  · simp [hp]
  · have hp1 : 1 ≤ C.param n x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp)
    rw [Nat.cast_sub hp1]
    ring

/-- The second raw moment coefficient is the cumulative square of the
parameter on the size-`n` fiber. -/
theorem ParamClass.coeff_rawMoment2 (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (rawMoment2 C.bgf) =
      ∑ x : C.Obj n, (C.param n x : ℚ) ^ 2 := by
  classical
  rw [rawMoment2, map_add]
  change PowerSeries.coeff n (factorialMoment2 C.bgf + factorialMoment1 C.bgf) =
    ∑ x : C.Obj n, (C.param n x : ℚ) ^ 2
  rw [map_add, ParamClass.coeff_factorialMoment2, ParamClass.coeff_factorialMoment1,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Mean and variance for ones in binary words

For length-`n` binary words, the number of ones has the binomial distribution
`Bin(n, 1/2)`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

private lemma counts_binaryWords (n : ℕ) :
    ParamClass.binaryWords.toCombClass.counts n = 2 ^ n := by
  rw [CombClass.counts, ParamClass.binaryWords]
  simp [Fintype.card_bool]

private lemma coeff_factorialMoment1_binaryWords (n : ℕ) :
    PowerSeries.coeff n (factorialMoment1 ParamClass.binaryWords.bgf) =
      ((n : ℚ) / 2) * (2 : ℚ) ^ n := by
  set_option backward.isDefEq.respectTransparency false in
    rcases n with _ | n
    · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords]
    · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords,
        Polynomial.derivative_pow, Polynomial.eval_pow]
      ring_nf

private lemma coeff_rawMoment2_binaryWords (n : ℕ) :
    PowerSeries.coeff n (rawMoment2 ParamClass.binaryWords.bgf) =
      ((n : ℚ) * ((n : ℚ) + 1) / 4) * (2 : ℚ) ^ n := by
  set_option backward.isDefEq.respectTransparency false in
    rcases n with _ | n
    · rw [ParamClass.coeff_rawMoment2]
      simp [ParamClass.binaryWords]
    rcases n with _ | n
    · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords,
        Polynomial.derivative_pow]
      norm_num
    · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf, paramPoly_binaryWords,
        Polynomial.derivative_pow, Polynomial.eval_pow]
      ring_nf

private lemma mean_binaryWords_all (n : ℕ) :
    ParamClass.binaryWords.mean n = (n : ℚ) / 2 := by
  rw [ParamClass.mean]
  rw [coeff_factorialMoment1_binaryWords n, counts_binaryWords]
  norm_num [Nat.cast_pow]

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open scoped Polynomial
open PowerSeries Finset
theorem solution {n : ℕ} :
    ParamClass.binaryWords.variance n = (n : ℚ) / 4 := by
  rw [ParamClass.variance]
  rw [coeff_rawMoment2_binaryWords n, mean_binaryWords_all n, counts_binaryWords]
  norm_num [Nat.cast_pow]
  ring
