-- Prove2me | Theorems.Thm_DeltaDense_card_filter_superset
-- name    : DeltaDense.card_filter_superset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:43:57.198193+00:00
-- url     : https://prove2.me/theorems/4e7ebf27-f687-46e6-9536-8091f548d553
-- title:
--   The number of `m`-element subsets of `[n]` containing a fixed subset `P` of `[n]` is
-- statement:
--   The number of `m`-element subsets of `[n]` containing a fixed subset `P` of `[n]` is
--   `C(n - |P|, m - |P|)`.
--
--   ```lean
--   theorem DeltaDense.card_filter_superset(n m : ℕ) {P : Finset ℕ} (hP : P ⊆ range n) (hPm : P.card ≤ m) :
--       (((range n).powersetCard m).filter (fun S => P ⊆ S)).card
--         = (n - P.card).choose (m - P.card) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/DeltaDenseSumsetAvoidance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/DeltaDenseSumsetAvoidance.lean#L165

-- Thm stub generated from Bridges/DeltaDenseSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
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

open DeltaDense

open Finset Pointwise

/-! ## Arithmetic progressions as finsets -/










/-! ## The counting estimates -/

theorem DeltaDense.card_filter_superset(n m : ℕ) {P : Finset ℕ} (hP : P ⊆ range n) (hPm : P.card ≤ m) :
    (((range n).powersetCard m).filter (fun S => P ⊆ S)).card
      = (n - P.card).choose (m - P.card) := by sorry
