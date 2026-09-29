-- Prove2me | Theorems.Thm_DeltaDense_eventually_exists_dense_avoiding_ap_sumsets
-- name    : DeltaDense.eventually_exists_dense_avoiding_ap_sumsets
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:36.356749+00:00
-- url     : https://prove2.me/theorems/03d9fca7-0494-45f5-9eb8-84f68c54e330
-- title:
--   Asymptotic packaging of `exists_dense_avoiding_ap_sumsets`: for every `0 < δ < 1`, for
-- statement:
--   Asymptotic packaging of `exists_dense_avoiding_ap_sumsets`: for every `0 < δ < 1`, for
--   all sufficiently large `n`, there is a `δ`-dense subset of `[n]` containing no sumset of
--   two arithmetic progressions of common length at least `3 log n / log (1/δ)`.
--
--   ```lean
--   theorem DeltaDense.eventually_exists_dense_avoiding_ap_sumsets(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
--       ∀ᶠ n : ℕ in Filter.atTop, ∃ S ⊆ range n, δ * n ≤ S.card ∧
--         ∀ a b d₁ d₂ k : ℕ, 0 < d₁ → 0 < d₂ →
--           3 * (Real.log n / Real.log (1 / δ)) ≤ k →
--           ¬ (apF a d₁ k + apF b d₂ k ⊆ S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/DeltaDenseSumsetAvoidance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/DeltaDenseSumsetAvoidance.lean#L528

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

theorem DeltaDense.eventually_exists_dense_avoiding_ap_sumsets(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ S ⊆ range n, δ * n ≤ S.card ∧
      ∀ a b d₁ d₂ k : ℕ, 0 < d₁ → 0 < d₂ →
        3 * (Real.log n / Real.log (1 / δ)) ≤ k →
        ¬ (apF a d₁ k + apF b d₂ k ⊆ S) := by sorry
