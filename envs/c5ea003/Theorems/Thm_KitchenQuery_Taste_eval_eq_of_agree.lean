-- Prove2me | Theorems.Thm_KitchenQuery_Taste_eval_eq_of_agree
-- name    : KitchenQuery.Taste.eval_eq_of_agree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:03:45.873764+00:00
-- url     : https://prove2.me/theorems/866dcb73-f82a-4f25-9e9b-835eda15dd52
-- title:
--   Path lemma, part 2.
-- statement:
--   **Path lemma, part 2.** The verdict only depends on the ingredients actually probed.
--
--   ```lean
--   theorem KitchenQuery.Taste.eval_eq_of_agree(t : Taste n) (x y : Pantry n)
--       (h : ∀ i ∈ t.path x, y i = x i) : t.eval y = t.eval x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KitchenQueryComplexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KitchenQueryComplexity.lean#L97

-- Thm stub generated from Novelty/KitchenQueryComplexity.lean
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

theorem KitchenQuery.Taste.eval_eq_of_agree(t : Taste n) (x y : Pantry n)
    (h : ∀ i ∈ t.path x, y i = x i) : t.eval y = t.eval x := by sorry
