-- Prove2me | Definitions.Def_Novelty_PermutationCompleteIntersection
-- name    : Novelty_PermutationCompleteIntersection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:35:48.638031+00:00
-- url     : https://prove2.me/theorems/8746929d-ef5b-4fee-ae60-5d8b594cbf27
-- title:
--   Aether Catalog definitions — Novelty_PermutationCompleteIntersection
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PermutationCompleteIntersection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PermutationCompleteIntersection.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_PermutationAgreement

/-!
# A large extremal `t`-intersecting family of permutations

Building on the fixed-point bridge of `PermutationAgreement`, this file proves
the **lower-bound half** of the permutation Complete Intersection Theorem
(Deza–Frankl 1977, Kupavskii 2022): for every `t` and `m` there is a
`t`-intersecting family of permutations of `Fin (t + m)` of size `m! = (t+m-t)!`.

A family is `t`-**intersecting** when every two members agree in at least `t`
coordinates.  The canonical extremal witness is the **prefix stabilizer**
`fixPrefix t m`, the permutations fixing each of the first `t` points; any two of
its members agree on all of `0, 1, …, t-1`, so it is `t`-intersecting, and it has
exactly `m!` elements because a permutation fixing the first `t` points is the
same data as a permutation of the remaining `m` points.

The cardinality is computed via `DomMulAct.stabilizer_card`, which expresses the
number of permutations preserving a function as the product of factorials of its
fiber sizes.

## Main results
* `PermIntersecting.card_fixPrefix` — `|fixPrefix t m| = m!`.
* `PermIntersecting.fixPrefix_tIntersecting` — `fixPrefix t m` is `t`-intersecting.
* `PermIntersecting.exists_extremal_tIntersecting` — existence of a
  `t`-intersecting family of permutations of `Fin (t+m)` of size `m!`.
* `PermIntersecting.exists_extremal_intersecting` — the `t = 1` corollary:
  an intersecting family of permutations of `Fin (1+m)` of size `m!` (the
  Deza–Frankl `(n-1)!` lower bound).

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
The `t`-intersecting extremal family should be a "dictatorship"-type object: fix
`t` coordinates.  Conjecture its size is exactly `(n-t)!` and it is genuinely
`t`-intersecting, matching the Complete Intersection Theorem prediction.

## Experiment (Experimenter)
`t=1, n=3`: permutations fixing `0` are `id` and `(1 2)`, i.e. `2! = 2`.  ✓
`t=2, n=4`: permutations fixing `0,1` are `id` and `(2 3)`, i.e. `2! = 2`.  ✓
`t=3, n=3`: only `id`, i.e. `0! = 1`.  ✓  The pattern `(n-t)!` holds.

## Analysis (Analyst)
Counting reduces to `DomMulAct.stabilizer_card` applied to the "collapse" map
`collapse t m : Fin (t+m) → Fin (t+1)`, identity below `t` and constant `t`
above.  Its fibers are `t` singletons and one block of size `m`, giving product
`1^t · m! = m!`.  The subtle step is that fixing the first `t` points is
*equivalent* to preserving `collapse` — the reverse direction needs
injectivity of `σ`.

## Critique (Critic)
Non-triviality: the theorem is not vacuous — `fixPrefix t m` is exhibited
explicitly and shown both large (`m!`) and `t`-intersecting.  Edge cases `m=0`
(family `= {id}`, size `1 = 0!`) and `t=0` (all permutations, size `(t+m)!`)
are covered by the same proof.

## Synthesis (Principal Investigator)
The lower-bound half of the permutation Complete Intersection Theorem is fully
constructive: `fixPrefix t m` witnesses `(n-t)!` and is provably `t`-intersecting.
Counting via `DomMulAct.stabilizer_card` (fiber factorials) is a clean, reusable
template for future extremal constructions where the family is the stabilizer of
a labelling.  The matching *upper* bound `(n-t)!` (Deza–Frankl / Ellis–Friedgut–
Pilpel) remains the deep open target, recorded in FUTURE_DIRECTIONS.
-/

open Equiv Function Finset

namespace PermIntersecting

variable {n : ℕ}

/-- A family of permutations is `t`-**intersecting** if any two members agree in
at least `t` coordinates. -/
def IsTIntersecting (t : ℕ) (F : Finset (Perm (Fin n))) : Prop :=
  ∀ σ ∈ F, ∀ τ ∈ F, t ≤ (agreements σ τ).card

/-- The **prefix stabilizer**: permutations of `Fin (t+m)` fixing each of the
first `t` points. -/
def fixPrefix (t m : ℕ) : Finset (Perm (Fin (t + m))) :=
  Finset.univ.filter (fun σ => ∀ i : Fin (t + m), (i : ℕ) < t → σ i = i)

/-- The **collapse map**: identity on the first `t` points, constant `t`
elsewhere.  Used to count `fixPrefix` via `DomMulAct.stabilizer_card`. -/
def collapse (t m : ℕ) : Fin (t + m) → Fin (t + 1) :=
  fun i => ⟨min (i : ℕ) t, Nat.lt_succ_of_le (min_le_right _ _)⟩


/-
Fixing the first `t` points is equivalent to preserving the collapse map.
-/

/-
Each fiber of `collapse` over a value `< t` is a singleton.
-/

/-
The fiber of `collapse` over the top value `t` has `m` elements.
-/

/-
**The prefix stabilizer has exactly `m!` members.**
-/

/-
The set of the first `t` coordinates, as a finset of `Fin (t+m)`.
-/

/-
**The prefix stabilizer is `t`-intersecting.**
-/



end PermIntersecting


