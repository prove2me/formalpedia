-- Prove2me | solution 1 for DeltaDense.card_filter_superset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:57.830962+00:00
-- url     : https://prove2.me/submissions/613d78b8-889c-46ad-bdab-2163b13011ec

-- Sol generated from Bridges/DeltaDenseSumsetAvoidance.lean
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







open DeltaDense in
theorem solution(n m : ℕ) {P : Finset ℕ} (hP : P ⊆ range n) (hPm : P.card ≤ m) :
    (((range n).powersetCard m).filter (fun S => P ⊆ S)).card
      = (n - P.card).choose (m - P.card) := by
  classical
  have hc := Finset.card_powersetCard (m - P.card) ((range n) \ P)
  rw [Finset.card_sdiff_of_subset hP, Finset.card_range] at hc
  rw [← hc]
  refine Finset.card_nbij' (fun S => S \ P) (fun U => U ∪ P) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard] at hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hS
    refine ⟨Finset.sdiff_subset_sdiff h1 (fun ⦃_⦄ h => h), ?_⟩
    rw [Finset.card_sdiff_of_subset h3, h2]
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard]
    obtain ⟨h1, h2⟩ := hU
    have hdisj : Disjoint U P := by
      refine Finset.disjoint_left.2 fun a ha haP => ?_
      have := h1 ha
      simp only [Finset.mem_sdiff] at this
      exact this.2 haP
    refine ⟨⟨Finset.union_subset (h1.trans Finset.sdiff_subset) hP, ?_⟩,
      Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, h2]
    omega
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hS
    exact Finset.sdiff_union_of_subset hS.2
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    have hdisj : Disjoint U P := by
      refine Finset.disjoint_left.2 fun a ha haP => ?_
      have := hU.1 ha
      simp only [Finset.mem_sdiff] at this
      exact this.2 haP
    exact Finset.union_sdiff_cancel_right hdisj
