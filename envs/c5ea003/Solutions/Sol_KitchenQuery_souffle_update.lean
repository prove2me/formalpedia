-- Prove2me | solution 1 for KitchenQuery.souffle_update
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:25:36.984703+00:00
-- url     : https://prove2.me/submissions/87ad2d86-6dc2-438b-bd40-a092c3c357c6

-- Sol generated from Novelty/KitchenQueryComplexity.lean
import Mathlib
import Definitions.Def_Novelty_KitchenQueryComplexity

/-!
# Kitchen query complexity: cooking, tasting, and an unconditional `P ≠ NP` in the kitchen

The slogan "a recipe is an algorithm, so `C(R)` versus `V(R)` is `P` versus `NP`" is
usually left as a metaphor.  This file makes the metaphor into a theorem by choosing a
computational model in which the separation is *provable*: the deterministic
**decision-tree (query) model**.

* A *pantry* of `n` ingredients is a Boolean vector `x : Fin n → Bool` (each ingredient is
  fresh/spoiled, whipped/flat, ...).
* A *dish* is a predicate `f : Pantry n → Bool`: is the result good?
* *Cooking* means touching all `n` ingredients: `C(R) = n`.
* *Tasting* is modelled by a `Taste` tree: adaptively probe individual ingredients of the
  finished dish and then declare it good or bad.  `V(R)` is the minimal depth of a taste
  tree computing `f` (`tasteCost`).
* *Nondeterministic verification* (a "garnish" pointing at what to taste) is certificate
  complexity: a set `S` of probes with `IsCertificate f x S`.

The main results are:

* `Taste.card_path_le_depth`, `Taste.eval_eq_of_agree`: the path lemma, the technical
  heart of every lower bound below.
* `sensitivity_le_tasteCost`: sensitivity is a lower bound on tasting time.
* `tasteCost_le_card_ingredients`: tasting is never slower than cooking, `V(R) ≤ C(R)`.
* `tasteCost_allFresh`: the "everything must be fresh" dish is *evasive*: `V = C = n`.
* `kitchen_P_ne_NP`: the anySpoiled dish has a one-probe nondeterministic certificate at
  every bad pantry, yet every deterministic taster needs all `n` probes.  This is an
  unconditional separation of deterministic and nondeterministic kitchen verification.
* `souffle_no_certificate_shortcut`: for the soufflé dish (parity of the pantry) *even*
  nondeterministic verification is useless — every certificate at every pantry is the whole
  pantry.  This is the honest version of "soufflé verification is co-NP-hard": the soufflé
  is hard to verify from *both* sides, unlike the salad.
* `tasteCost_zero_iff_constant`: you cannot tell whether the soufflé rose without cutting
  into it.

No claim about Navier–Stokes or `PSPACE` is made: those need a physical model that timing
data does not supply.  What *is* proved is the exact combinatorial shadow of the
conjecture.
-/

open KitchenQuery

open Finset




open Taste

variable {n : ℕ}








variable {n : ℕ}


/-! ### Brute-force tasting: cooking-time verification always works -/





/-! ### Verification cost -/









/-! ### Sensitivity: the universal lower bound on tasting -/







/-! ### Nondeterministic verification: certificates -/






/-! ### Three model dishes -/










/-! ### The soufflé: parity, hard from both sides -/








open KitchenQuery in
theorem solution(x : Pantry n) (i : Fin n) :
    souffle (Function.update x i (!x i)) ≠ souffle x := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hx : (∑ j, if x j then 1 else 0)
      = (if x i then 1 else 0) + ∑ j ∈ Finset.univ.erase i, if x j then 1 else 0 := by
    rw [← Finset.add_sum_erase _ _ hmem]
  have hu : (∑ j, if Function.update x i (!x i) j then 1 else 0)
      = (if !x i then 1 else 0) + ∑ j ∈ Finset.univ.erase i, if x j then 1 else 0 := by
    rw [← Finset.add_sum_erase _ _ hmem]
    simp only [Function.update_self]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hne]
  simp only [souffle, ne_eq, decide_eq_decide, Nat.odd_iff, hx, hu]
  cases hxi : x i <;> simp <;> omega
