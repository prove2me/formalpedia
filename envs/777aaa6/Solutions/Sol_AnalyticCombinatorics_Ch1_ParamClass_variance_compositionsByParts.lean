-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.ParamClass.variance_compositionsByParts
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:33:36.500027+00:00
-- url     : https://prove2.me/submissions/5d5afd4a-ef48-49d9-9abb-ddb9f50845c3

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Variance
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

@[simp] lemma CombClass.counts_compositions (n : ℕ) :
    CombClass.compositions.counts n = 2 ^ (n - 1) :=
  composition_card n

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

/-- The mean is the cumulative parameter divided by the number of objects. -/
theorem ParamClass.mean_eq (C : ParamClass) (n : ℕ) :
    C.mean n = (∑ x : C.Obj n, (C.param n x : ℚ)) / (C.toCombClass.counts n : ℚ) := by
  rw [ParamClass.mean, ParamClass.coeff_factorialMoment1]

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

/-- The variance is the normalized second raw moment minus the squared mean. -/
theorem ParamClass.variance_eq (C : ParamClass) (n : ℕ) :
    C.variance n =
      (∑ x : C.Obj n, (C.param n x : ℚ) ^ 2) / (C.toCombClass.counts n : ℚ) -
        C.mean n ^ 2 := by
  rw [ParamClass.variance, ParamClass.coeff_rawMoment2]

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Mean and variance for parts in compositions

For a fixed `n ≥ 1`, Mathlib's boundary-set equivalence identifies
compositions of `n` with subsets of `Fin (n - 1)`.  The number of parts is one
plus the number of chosen interior boundaries.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

private lemma compositionAsSetEquiv_symm_length (n : ℕ) (h : 0 < n)
    (s : Finset (Fin (n - 1))) :
    (((compositionAsSetEquiv n).symm s).length) = s.card + 1 := by
  let e : Fin (n - 1) ↪ Fin (n + 1) :=
    ⟨fun j => ⟨(j : ℕ) + 1, by omega⟩, by
      intro a b hab
      ext
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hab
      simp at this
      omega⟩
  let p : Fin (n + 1) → Prop :=
    fun i => i = 0 ∨ i = Fin.last n ∨ ∃ j ∈ s, (i : ℕ) = (j : ℕ) + 1
  have hset : (Finset.univ.filter p) = insert 0 (insert (Fin.last n) (s.map e)) := by
    ext i
    constructor
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p] at hi
      rcases hi with h0 | hlast | ⟨j, hj, hval⟩
      · simp [h0]
      · simp [hlast]
      · rw [Finset.mem_insert, Finset.mem_insert]
        right
        right
        exact Finset.mem_map.mpr ⟨j, hj, by
          ext
          simp [e, hval]⟩
    · intro hi
      rw [Finset.mem_insert, Finset.mem_insert] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p]
      rcases hi with h0 | hlast | himage
      · exact Or.inl h0
      · exact Or.inr (Or.inl hlast)
      · rcases Finset.mem_map.mp himage with ⟨j, hj, hji⟩
        exact Or.inr (Or.inr ⟨j, hj, by
          have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hji.symm
          simpa [e] using this⟩)
  have hlast_ne_zero : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro hz
    have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hz
    simp at this
    omega
  have hzero_not_map : (0 : Fin (n + 1)) ∉ s.map e := by
    intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hj_eq⟩
    have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hj_eq
    simp [e] at this
  have hlast_not_map : (Fin.last n : Fin (n + 1)) ∉ s.map e := by
    intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hj_eq⟩
    have hjlt : (j : ℕ) < n - 1 := j.2
    have hv : (j : ℕ) + 1 = n := by
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hj_eq
      simpa [e] using this
    omega
  have hzero_not_insert : (0 : Fin (n + 1)) ∉ insert (Fin.last n) (s.map e) := by
    simp [Ne.symm hlast_ne_zero, hzero_not_map]
  simp [compositionAsSetEquiv, CompositionAsSet.length]
  change (Finset.univ.filter p).card = s.card + 2
  rw [hset]
  rw [Finset.card_insert_of_notMem hzero_not_insert]
  rw [Finset.card_insert_of_notMem hlast_not_map]
  simp

private lemma compositionEquiv_symm_length (n : ℕ) (h : 0 < n)
    (s : Finset (Fin (n - 1))) :
    (((compositionEquiv n).symm ((compositionAsSetEquiv n).symm s)).length) =
      s.card + 1 := by
  simpa [compositionEquiv] using compositionAsSetEquiv_symm_length n h s

private lemma sum_pow_card_finset (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ s : Finset α, (Polynomial.X : ℚ[X]) ^ s.card) =
      (1 + Polynomial.X) ^ Fintype.card α := by
  simpa [Finset.prod_eq_pow_card] using
    (Finset.prod_one_add (s := (Finset.univ : Finset α))
      (f := fun _ : α => (Polynomial.X : ℚ[X]))).symm

private lemma paramPoly_compositionsByParts_pos (n : ℕ) (h : 0 < n) :
    ParamClass.compositionsByParts.paramPoly n =
      Polynomial.X * (1 + Polynomial.X : ℚ[X]) ^ (n - 1) := by
  classical
  rw [ParamClass.paramPoly, ParamClass.compositionsByParts]
  change (∑ c : Composition n, (Polynomial.X : ℚ[X]) ^ c.length) =
    Polynomial.X * (1 + Polynomial.X : ℚ[X]) ^ (n - 1)
  let eComp : Composition n ≃ Finset (Fin (n - 1)) :=
    (compositionEquiv n).trans (compositionAsSetEquiv n)
  calc
    (∑ c : Composition n, (Polynomial.X : ℚ[X]) ^ c.length)
        = ∑ s : Finset (Fin (n - 1)),
            (Polynomial.X : ℚ[X]) ^ ((eComp.symm s).length) := by
          simpa using
            (Equiv.sum_comp eComp.symm
              (fun c : Composition n => (Polynomial.X : ℚ[X]) ^ c.length)).symm
    _ = ∑ s : Finset (Fin (n - 1)),
            (Polynomial.X : ℚ[X]) ^ (s.card + 1) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [eComp, compositionEquiv_symm_length n h s]
    _ = Polynomial.X * ∑ s : Finset (Fin (n - 1)),
            (Polynomial.X : ℚ[X]) ^ s.card := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [pow_succ']
    _ = Polynomial.X * (1 + Polynomial.X : ℚ[X]) ^ (n - 1) := by
          rw [sum_pow_card_finset]
          simp

private lemma coeff_factorialMoment1_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (factorialMoment1 ParamClass.compositionsByParts.bgf) =
      (((n : ℚ) + 1) / 2) * (2 : ℚ) ^ (n - 1) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos 1 (by omega)]
  · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos (n + 2) (by omega),
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.eval_pow]
    set_option backward.isDefEq.respectTransparency false in
      ring_nf

private lemma coeff_rawMoment2_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (rawMoment2 ParamClass.compositionsByParts.bgf) =
      ((n : ℚ) * ((n : ℚ) + 3) / 4) * (2 : ℚ) ^ (n - 1) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos 1 (by omega)]
    norm_num
  rcases n with _ | n
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos 2 (by omega), Polynomial.derivative_mul]
    norm_num
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos (n + 3) (by omega),
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.eval_pow]
    set_option backward.isDefEq.respectTransparency false in
      ring_nf

theorem ParamClass.mean_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.compositionsByParts.mean n = ((n : ℚ) + 1) / 2 := by
  rw [ParamClass.mean_eq]
  rw [← ParamClass.coeff_factorialMoment1 ParamClass.compositionsByParts n,
    coeff_factorialMoment1_compositionsByParts hn]
  simp [ParamClass.compositionsByParts, CombClass.counts_compositions]

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open scoped Polynomial
open PowerSeries Finset
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.compositionsByParts.variance n = ((n : ℚ) - 1) / 4 := by
  rw [ParamClass.variance_eq]
  rw [← ParamClass.coeff_rawMoment2 ParamClass.compositionsByParts n,
    coeff_rawMoment2_compositionsByParts hn, ParamClass.mean_compositionsByParts hn]
  simp [ParamClass.compositionsByParts, CombClass.counts_compositions]
  ring
