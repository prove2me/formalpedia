-- Prove2me | Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
-- name    : Bridges_DeltaDenseSumsetAvoidance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:32.276446+00:00
-- url     : https://prove2.me/theorems/2b0681f3-db16-4646-ab2c-6c31f2c6eb4b
-- title:
--   Aether Catalog definitions — Bridges_DeltaDenseSumsetAvoidance
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.DeltaDenseSumsetAvoidance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/DeltaDenseSumsetAvoidance.lean by skeleton subtraction
import Mathlib
/-
# δ-dense sets avoiding large arithmetic sumsets

This file develops, from scratch, a rigorous finitary construction related to the
sharpness of "sumset in a dense set" theorems (Kra–Moreira–Richter–Robertson type
statements, whose finitary form predicts that a set `S ⊆ [n]` of density `δ` should
contain a sumset `A + B` with `min(|A|,|B|) ≍ log n / log (1/δ)`).

The content here is the *sharpness* side.  For every `0 < δ < 1` and every sufficiently
large `n` we construct a set `S ⊆ [n]` with `|S| ≥ δ n` such that

* `S` contains **no** arithmetic progression of length `(5/2)·log n / log (1/δ)`
  (`DeltaDense.exists_dense_no_ap`),
* `S` contains **no** sumset `A + B` with `A` an arbitrary nonempty finite set and `B` an
  arithmetic progression of length at least `(5/2)·log n / log (1/δ)`
  (`DeltaDense.exists_dense_no_sumset_with_ap`), and
* `S` contains **no** sumset `A + B` where `A` and `B` are arithmetic progressions —
  with *arbitrary, possibly different* positive common differences — of common length
  `k ≥ 3 log n / log (1/δ)`
  (`DeltaDense.exists_dense_avoiding_ap_sumsets`, and its asymptotic packaging
  `DeltaDense.eventually_exists_dense_avoiding_ap_sumsets`).

The second statement realises the constant `C(δ) = 3` from the conjectural picture: `3`
is exactly the number of parameters `(t, d₁, d₂)` needed to describe the "L-shaped"
witness `{t, t+d₁, …, t+(k-1)d₁} ∪ {t+(k-1)d₁, …, t+(k-1)d₁+(k-1)d₂}` of `2k-1` elements
that any such sumset must contain, so the first-moment union bound costs `n³`.

The proof is a purely counting ("derandomised probabilistic method") argument over the
family of `m`-element subsets of `[n]`:

* `DeltaDense.choose_ratio_sub` : `C(n-L, m-L) · n^L ≤ C(n,m) · m^L`, the integer form of
  the estimate `P(fixed L-set ⊆ random m-subset) ≤ (m/n)^L`;
* `DeltaDense.card_filter_superset` : the number of `m`-subsets of `[n]` containing a
  fixed `L`-set is `C(n-L, m-L)`;
* `DeltaDense.exists_card_eq_avoiding_family` : the general first-moment principle — if a
  family of `|I|` sets, each of size at least `L`, satisfies `|I|·m^L < n^L`, then some
  `m`-element subset of `[n]` contains none of them;
* `DeltaDense.pow_cond` : the analytic verification of `n^c·m^L < n^L` for `m = ⌈δn⌉`.
-/

namespace DeltaDense

open Finset Pointwise

/-! ## Arithmetic progressions as finsets -/

/-- The arithmetic progression `{a, a+d, …, a+(L-1)d}`, as a `Finset ℕ`. -/
def apF (a d L : ℕ) : Finset ℕ := (range L).image (fun i => a + d * i)






/-- The "L-shaped" subset of the two-dimensional grid `{t + i d₁ + j d₂ : i, j < k}`:
the first row together with the last column.  It has `2k - 1` elements. -/
def gridWitness (t d₁ d₂ k : ℕ) : Finset ℕ :=
  apF t d₁ k ∪ apF (t + d₁ * (k - 1)) d₂ k



/-! ## The counting estimates -/




/-! ## The general first-moment principle -/


/-! ## Progression-free and grid-free dense sets, in integer form -/



/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no long progressions and no progression sumsets -/






end DeltaDense


