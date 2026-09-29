-- Prove2me | Definitions.Def_Novelty_KitchenQueryComplexity
-- name    : Novelty_KitchenQueryComplexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:51.314115+00:00
-- url     : https://prove2.me/theorems/009eb4c9-ac3f-43df-96fe-a8aadf7e81da
-- title:
--   Aether Catalog definitions — Novelty_KitchenQueryComplexity
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KitchenQueryComplexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KitchenQueryComplexity.lean by skeleton subtraction
import Mathlib

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

namespace KitchenQuery

open Finset

/-- A pantry state: each of the `n` ingredients is in one of two conditions. -/
abbrev Pantry (n : ℕ) := Fin n → Bool

/-- A dish: the predicate "this pantry cooks up to something good". -/
abbrev Dish (n : ℕ) := Pantry n → Bool

/-- An adaptive tasting strategy: probe an ingredient of the dish, branch, and Filter.eventually
serve a verdict. -/
inductive Taste (n : ℕ) where
  | serve : Bool → Taste n
  | probe : Fin n → Taste n → Taste n → Taste n
  deriving Inhabited

namespace Taste

variable {n : ℕ}

/-- Worst-case number of probes. -/
def depth : Taste n → ℕ
  | serve _ => 0
  | probe _ l r => 1 + max l.depth r.depth

/-- The verdict of a tasting strategy on a pantry. -/
def eval : Taste n → Pantry n → Bool
  | serve b, _ => b
  | probe i l r, x => if x i then eval r x else eval l x

/-- The set of ingredients actually probed on the pantry `x`. -/
def path : Taste n → Pantry n → Finset (Fin n)
  | serve _, _ => ∅
  | probe i l r, x => insert i (if x i then path r x else path l x)




end Taste

variable {n : ℕ}

/-- A tasting strategy decides a dish. -/
def Computes (t : Taste n) (f : Dish n) : Prop := ∀ x, t.eval x = f x

/-! ### Brute-force tasting: cooking-time verification always works -/

/-- The exhaustive taster that probes ingredients `0, …, k-1`, starting from the default
guess `a` for the untouched ones. -/
def brute (f : Dish n) : ℕ → Pantry n → Taste n
  | 0, a => .serve (f a)
  | (k + 1), a =>
      if h : k < n then
        .probe ⟨k, h⟩ (brute f k (Function.update a ⟨k, h⟩ false))
          (brute f k (Function.update a ⟨k, h⟩ true))
      else brute f k a




/-! ### Verification cost -/

/-- The set of achievable tasting depths for a dish. -/
def tasteDepths (f : Dish n) : Set ℕ := {d | ∃ t : Taste n, Computes t f ∧ t.depth ≤ d}


/-- **Verification time `V(R)`**: the least number of probes of a worst-case-optimal
adaptive taster. -/
noncomputable def tasteCost (f : Dish n) : ℕ := sInf (tasteDepths f)

/-- **Cooking time `C(R)`**: every one of the `n` ingredients must be handled. -/
def cookCost (_f : Dish n) : ℕ := n





/-! ### Sensitivity: the universal lower bound on tasting -/

/-- Ingredient `i` is *pivotal* for the dish `f` at the pantry `x` if swapping it alone
changes the verdict. -/
def Pivotal (f : Dish n) (x : Pantry n) (i : Fin n) : Prop :=
  f (Function.update x i (!x i)) ≠ f x

instance (f : Dish n) (x : Pantry n) (i : Fin n) : Decidable (Pivotal f x i) := by
  unfold Pivotal; infer_instance

/-- The pivotal ingredients at a pantry (the *sensitivity* set). -/
def pivotalSet (f : Dish n) (x : Pantry n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Pivotal f x i)




/-! ### Nondeterministic verification: certificates -/

/-- A *garnish certificate*: probing the ingredients in `S` already pins the verdict. -/
def IsCertificate (f : Dish n) (x : Pantry n) (S : Finset (Fin n)) : Prop :=
  ∀ y, (∀ i ∈ S, y i = x i) → f y = f x





/-! ### Three model dishes -/



/-- **The one-ingredient salad**: good iff the single flagged ingredient is fresh. -/
def salad (i : Fin n) : Dish n := fun x => x i


/-- **`anySpoiled`**: the dish is bad as soon as one ingredient is spoiled.  (Written as an
OR over the pantry.) -/
def anySpoiled : Dish n := fun x => decide (∃ i, x i = true)





/-! ### The soufflé: parity, hard from both sides -/

/-- The soufflé verdict: it rises exactly when an odd number of the `n` critical steps were
performed correctly — a parity, the canonical "no partial information" dish. -/
def souffle : Dish n := fun x => decide (Odd (∑ i, if x i then 1 else 0))






end KitchenQuery


