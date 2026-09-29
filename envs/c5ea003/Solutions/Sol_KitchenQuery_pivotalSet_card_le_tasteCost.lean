-- Prove2me | solution 1 for KitchenQuery.pivotalSet_card_le_tasteCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:18:21.868217+00:00
-- url     : https://prove2.me/submissions/60091fa6-c70b-4ba6-a7b3-8335654951d2

-- Sol generated from Novelty/KitchenQueryComplexity.lean
import Mathlib
import Definitions.Def_Novelty_KitchenQueryComplexity
import Theorems.Thm_KitchenQuery_Taste_card_path_le_depth
import Theorems.Thm_KitchenQuery_Taste_eval_eq_of_agree
import Theorems.Thm_KitchenQuery_exists_optimal_taste

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




/-- Every pivotal ingredient must actually be probed. -/
theorem pivotal_mem_path {t : Taste n} {f : Dish n} (ht : Computes t f) (x : Pantry n)
    {i : Fin n} (hi : Pivotal f x i) : i ∈ t.path x := by
  by_contra hmem
  set y := Function.update x i (!x i) with hy
  have hagree : ∀ j ∈ t.path x, y j = x j := by
    intro j hj
    have hne : j ≠ i := by rintro rfl; exact hmem hj
    simp [hy, Function.update_of_ne hne]
  have : f y = f x := by
    rw [← ht y, ← ht x]
    exact t.eval_eq_of_agree x y hagree
  exact hi this



/-! ### Nondeterministic verification: certificates -/






/-! ### Three model dishes -/










/-! ### The soufflé: parity, hard from both sides -/








open KitchenQuery in
theorem solution(f : Dish n) (x : Pantry n) :
    (pivotalSet f x).card ≤ tasteCost f := by
  obtain ⟨t, ht, hd⟩ := exists_optimal_taste f
  refine le_trans (le_trans (Finset.card_le_card ?_) (t.card_path_le_depth x)) hd
  intro i hi
  exact pivotal_mem_path ht x (by simpa [pivotalSet] using hi)
