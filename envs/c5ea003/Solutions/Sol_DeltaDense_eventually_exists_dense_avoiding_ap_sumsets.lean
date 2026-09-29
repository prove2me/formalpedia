-- Prove2me | solution 1 for DeltaDense.eventually_exists_dense_avoiding_ap_sumsets
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:30:24.453918+00:00
-- url     : https://prove2.me/submissions/2f0eb372-bb4c-40db-890d-403e23523f96

-- Sol generated from Bridges/DeltaDenseSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Theorems.Thm_DeltaDense_exists_dense_avoiding_ap_sumsets
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







open DeltaDense in
theorem solution(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ S ⊆ range n, δ * n ≤ S.card ∧
      ∀ a b d₁ d₂ k : ℕ, 0 < d₁ → 0 < d₂ →
        3 * (Real.log n / Real.log (1 / δ)) ≤ k →
        ¬ (apF a d₁ k + apF b d₂ k ⊆ S) := by
  have hlpos : 0 < Real.log (1 / δ) := by
    simp only [one_div]
    exact Real.log_pos (by rw [lt_inv_comm₀ (by norm_num) h0]; simpa using h1)
  rw [Filter.eventually_atTop]
  refine ⟨max 2 (max ⌈1 / δ ^ 2⌉₊ ⌈100 / (δ * Real.log (1 / δ))⌉₊), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hA : ⌈1 / δ ^ 2⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right 2 _)) hn
  have hB : ⌈100 / (δ * Real.log (1 / δ))⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right 2 _)) hn
  have hδn : 1 ≤ δ ^ 2 * n := by
    have h1n : 1 / δ ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hA)
    rw [div_le_iff₀ (by positivity)] at h1n
    linarith
  have hbig : 100 ≤ δ * n * Real.log (1 / δ) := by
    have h2n : 100 / (δ * Real.log (1 / δ)) ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hB)
    rw [div_le_iff₀ (by positivity)] at h2n
    nlinarith [h2n]
  exact exists_dense_avoiding_ap_sumsets δ h0 h1 hn2 hδn hbig
