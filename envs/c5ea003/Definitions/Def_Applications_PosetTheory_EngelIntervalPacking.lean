-- Prove2me | Definitions.Def_Applications_PosetTheory_EngelIntervalPacking
-- name    : Applications_PosetTheory_EngelIntervalPacking
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:24.35654+00:00
-- url     : https://prove2.me/theorems/0898803f-55a9-46dc-be1b-e4a519fb8c9b
-- title:
--   Aether Catalog definitions — Applications_PosetTheory_EngelIntervalPacking
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PosetTheory.EngelIntervalPacking`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PosetTheory/EngelIntervalPacking.lean by skeleton subtraction
import Mathlib
/-
# Engel's Interval Packing Theorem — constructions, thresholds, and a contrarian analysis

Engel's interval packing problem concerns the Boolean lattice `2^[n]` restricted to
the levels `l, l+1, …, l+r`.  An *interval* is a set of the form `[T, T ∪ C]` where
`T` is an `l`-element "bottom" and `C` is an `r`-element set disjoint from `T`; the
top is `T ∪ C` (of size `l + r`).  Two intervals `[T₁, T₁ ∪ C₁]`, `[T₂, T₂ ∪ C₂]`
are **disjoint** (as sub-posets of the Boolean lattice) exactly when there is no set
`S` lying in both, and one checks that

  `[T₁,B₁] ∩ [T₂,B₂] ≠ ∅  ↔  (T₁ ⊆ B₂ ∧ T₂ ⊆ B₁)`,

where `Bᵢ = Tᵢ ∪ Cᵢ` (the witness being `S = T₁ ∪ T₂`).  A collection of pairwise
disjoint intervals, one for **every** `l`-set `T`, is an interval packing of the
maximum possible size `C(n, l)` (one interval per level-`l` element).

Engel's theorem: such a maximum packing exists whenever `n ≥ (l+1)·r + l`.

This file develops the theory around the correct (disjointness) formulation and
proves several genuine results:

* `IsMaxIntervalPacking` — the correct notion (pairwise interval **disjointness**).
* `engel_r_zero` — the `r = 0` case for all `n, l`: the singleton intervals `{T}`
  form a maximum packing.
* `cycC` and `engel_l_one` — the `l = 1` case: an explicit **cyclic** construction
  `C_{t} = {t+1, …, t+r} (mod n)` gives a maximum packing whenever `n ≥ 2r + 1`,
  which is exactly the Engel threshold `(l+1)r + l` at `l = 1`.
* `no_maxpacking_two_one_one` — a **disproof** below the threshold: for
  `n = 2, l = 1, r = 1` (so `n = 2 < 3 = (l+1)r+l`) *no* maximum packing exists.
* `IsNaivePacking` and `naive_packing_impossible` — a contrarian observation: the
  *literal* reading of the informal statement (asking for `T₁ ⊄ B₂` **and**
  `T₂ ⊄ B₁` for **all** distinct pairs) is unsatisfiable as soon as `l, r ≥ 1`.
  This is why the disjointness formulation `¬(T₁ ⊆ B₂ ∧ T₂ ⊆ B₁)` is the right one.
-/

open Finset

namespace EngelIntervalPacking

/-- `T` is an `l`-element subset of the ground set `[n] = {0, …, n-1}`. -/
def IsLSet (n l : ℕ) (T : Finset ℕ) : Prop := T ⊆ Finset.range n ∧ T.card = l

/-- The interval `[T, T ∪ f T]`, for `T` an `l`-set, is a valid interval of "height"
`r`: its `C`-part `f T` is an `r`-set of the ground set, disjoint from `T`. -/
def IsValidAssignment (n l r : ℕ) (f : Finset ℕ → Finset ℕ) : Prop :=
  ∀ T, IsLSet n l T → f T ⊆ Finset.range n ∧ (f T).card = r ∧ Disjoint T (f T)

/-- A **maximum interval packing**: an assignment `f` (of an `r`-set `C_T = f T` to
every `l`-set `T`) whose intervals `[T, T ∪ f T]` are pairwise **disjoint**.  Two
intervals meet iff `T₁ ⊆ T₂ ∪ f T₂ ∧ T₂ ⊆ T₁ ∪ f T₁`, so disjointness is the
negation of that conjunction.  Because there is one interval for every `l`-set, the
packing has the maximum possible size `C(n, l)`. -/
def IsMaxIntervalPacking (n l r : ℕ) (f : Finset ℕ → Finset ℕ) : Prop :=
  IsValidAssignment n l r f ∧
    ∀ T₁, IsLSet n l T₁ → ∀ T₂, IsLSet n l T₂ → T₁ ≠ T₂ →
      ¬ (T₁ ⊆ T₂ ∪ f T₂ ∧ T₂ ⊆ T₁ ∪ f T₁)

/-! ## The `r = 0` case: singleton intervals -/


/-! ## The `l = 1` case: an explicit cyclic construction -/

/-- The cyclic `C`-set anchored at `a`: the `r` elements `a+1, a+2, …, a+r` taken
modulo `n`.  For `l = 1` and a bottom `T = {a}` we take `C_T = cycC n r a`. -/
def cycC (n r a : ℕ) : Finset ℕ := (Finset.range r).image (fun j => (a + 1 + j) % n)






/-
**Engel's theorem, `l = 1`.**  For `n ≥ 2r + 1`, assigning to each singleton
`T = {a}` the cyclic `r`-set `C_T = {a+1, …, a+r} (mod n)` yields a maximum interval
packing of the levels `1, …, 1+r`.  The threshold `2r + 1` is exactly `(l+1)r + l`
at `l = 1`.
-/

/-! ## A disproof below the threshold -/


/-! ## Contrarian analysis: the naive literal reading is impossible -/

/-- The **naive** (literal) reading of the informal statement: for every ordered pair
of distinct `l`-sets one asks `T₁ ⊄ T₂ ∪ f T₂` *and* `T₂ ⊄ T₁ ∪ f T₁`.  (Compare the
correct `IsMaxIntervalPacking`, which negates the *conjunction*.) -/
def IsNaivePacking (n l r : ℕ) (f : Finset ℕ → Finset ℕ) : Prop :=
  IsValidAssignment n l r f ∧
    ∀ T₁, IsLSet n l T₁ → ∀ T₂, IsLSet n l T₂ → T₁ ≠ T₂ →
      ¬ (T₁ ⊆ T₂ ∪ f T₂) ∧ ¬ (T₂ ⊆ T₁ ∪ f T₁)


end EngelIntervalPacking


