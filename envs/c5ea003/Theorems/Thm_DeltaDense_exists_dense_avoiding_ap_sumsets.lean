-- Prove2me | Theorems.Thm_DeltaDense_exists_dense_avoiding_ap_sumsets
-- name    : DeltaDense.exists_dense_avoiding_ap_sumsets
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:25.260549+00:00
-- url     : https://prove2.me/theorems/9e252bd2-19a9-4c3a-a98e-afef473aabca
-- title:
--   Main theorem (sharpness with `C(δ) = 3`).
-- statement:
--   **Main theorem (sharpness with `C(δ) = 3`).**  For every `0 < δ < 1` and every
--   sufficiently large `n` (it suffices that `δ² n ≥ 1` and `δ n log (1/δ) ≥ 100`) there is a
--   set `S ⊆ [n]` with `|S| ≥ δ n` such that for *all* pairs of arithmetic progressions
--   `A = {a, a+d₁, …}` and `B = {b, b+d₂, …}` with arbitrary positive common differences
--   `d₁, d₂` and common length `k ≥ 3 log n / log (1/δ)`, the sumset `A + B` is **not**
--   contained in `S`.
--
--   Progressions are the extremal shape for this problem: `A + B` is then a two-dimensional
--   grid, containing an L-shaped configuration of `2k-1` points described by only three
--   parameters `(t, d₁, d₂)`, whence the union bound of size `n³` and the constant `3`.
--
--   ```lean
--   theorem DeltaDense.exists_dense_avoiding_ap_sumsets(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) {n : ℕ}
--       (hn2 : 2 ≤ n) (hδn : 1 ≤ δ ^ 2 * n) (hbig : 100 ≤ δ * n * Real.log (1 / δ)) :
--       ∃ S ⊆ range n, δ * n ≤ S.card ∧
--         ∀ a b d₁ d₂ k : ℕ, 0 < d₁ → 0 < d₂ →
--           3 * (Real.log n / Real.log (1 / δ)) ≤ k →
--           ¬ (apF a d₁ k + apF b d₂ k ⊆ S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/DeltaDenseSumsetAvoidance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/DeltaDenseSumsetAvoidance.lean#L466

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




/-! ## The general first-moment principle -/


/-! ## Progression-free and grid-free dense sets, in integer form -/



/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no long progressions and no progression sumsets -/

theorem DeltaDense.exists_dense_avoiding_ap_sumsets(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) {n : ℕ}
    (hn2 : 2 ≤ n) (hδn : 1 ≤ δ ^ 2 * n) (hbig : 100 ≤ δ * n * Real.log (1 / δ)) :
    ∃ S ⊆ range n, δ * n ≤ S.card ∧
      ∀ a b d₁ d₂ k : ℕ, 0 < d₁ → 0 < d₂ →
        3 * (Real.log n / Real.log (1 / δ)) ≤ k →
        ¬ (apF a d₁ k + apF b d₂ k ⊆ S) := by sorry
