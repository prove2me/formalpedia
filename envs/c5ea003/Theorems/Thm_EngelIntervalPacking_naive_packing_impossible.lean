-- Prove2me | Theorems.Thm_EngelIntervalPacking_naive_packing_impossible
-- name    : EngelIntervalPacking.naive_packing_impossible
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:30.691025+00:00
-- url     : https://prove2.me/theorems/74d61e05-5ca9-4422-9544-761dd15b8c92
-- title:
--   Contrarian result.
-- statement:
--   **Contrarian result.**  Whenever `1 ≤ l ≤ n` and `1 ≤ r`, the naive literal
--   reading is unsatisfiable: any top `B = T ∪ f T` has size `l + r > l`, so it contains
--   some *other* `l`-set `T'` (`T' = T \ {t} ∪ {c}`), and `T' ⊆ B` contradicts the naive
--   demand.  This shows the disjointness formulation is the mathematically correct one.
--
--   ```lean
--   theorem EngelIntervalPacking.naive_packing_impossible(n l r : ℕ) (hl : 1 ≤ l) (hln : l ≤ n) (hr : 1 ≤ r) :
--       ¬ ∃ f, IsNaivePacking n l r f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EngelIntervalPacking.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EngelIntervalPacking.lean#L152

-- Thm stub generated from Applications/PosetTheory/EngelIntervalPacking.lean
import Mathlib
import Definitions.Def_Applications_PosetTheory_EngelIntervalPacking
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

open EngelIntervalPacking




/-! ## The `r = 0` case: singleton intervals -/


/-! ## The `l = 1` case: an explicit cyclic construction -/







/-
**Engel's theorem, `l = 1`.**  For `n ≥ 2r + 1`, assigning to each singleton
`T = {a}` the cyclic `r`-set `C_T = {a+1, …, a+r} (mod n)` yields a maximum interval
packing of the levels `1, …, 1+r`.  The threshold `2r + 1` is exactly `(l+1)r + l`
at `l = 1`.
-/

/-! ## A disproof below the threshold -/


/-! ## Contrarian analysis: the naive literal reading is impossible -/

theorem EngelIntervalPacking.naive_packing_impossible(n l r : ℕ) (hl : 1 ≤ l) (hln : l ≤ n) (hr : 1 ≤ r) :
    ¬ ∃ f, IsNaivePacking n l r f := by sorry
