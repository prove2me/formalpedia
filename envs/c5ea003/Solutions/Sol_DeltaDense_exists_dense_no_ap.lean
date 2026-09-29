-- Prove2me | solution 1 for DeltaDense.exists_dense_no_ap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:49.260176+00:00
-- url     : https://prove2.me/submissions/3d7178e5-4bd3-48ce-a2ed-ffa9bb63acc3

-- Sol generated from Bridges/DeltaDenseSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Theorems.Thm_DeltaDense_exists_card_eq_no_ap
import Theorems.Thm_DeltaDense_pow_cond
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




lemma apF_mono (a d : ℕ) {L M : ℕ} (h : L ≤ M) : apF a d L ⊆ apF a d M :=
  Finset.image_subset_image (by simpa using h)






/-! ## The counting estimates -/




/-! ## The general first-moment principle -/


/-! ## Progression-free and grid-free dense sets, in integer form -/



/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no long progressions and no progression sumsets -/







open DeltaDense in
theorem solution(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) {n : ℕ} (hn2 : 2 ≤ n)
    (hδn : 1 ≤ δ * n) (hbig : 100 ≤ δ * n * Real.log (1 / δ)) :
    ∃ S ⊆ range n, δ * n ≤ S.card ∧
      ∀ L : ℕ, (5 / 2) * (Real.log n / Real.log (1 / δ)) ≤ L →
        ∀ a d : ℕ, 0 < d → ¬ (apF a d L ⊆ S) := by
  have hlpos : 0 < Real.log (1 / δ) := by
    simp only [one_div]
    exact Real.log_pos (by rw [lt_inv_comm₀ (by norm_num) h0]; simpa using h1)
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hR1 : 1 ≤ Real.log n / Real.log (1 / δ) := by
    have hle : 1 / δ ≤ (n : ℝ) := by
      rw [div_le_iff₀ h0]; linarith [hδn]
    have := Real.log_le_log (by positivity) hle
    rw [le_div_iff₀ hlpos]
    linarith
  set L₀ : ℕ := ⌈(5 / 2) * (Real.log n / Real.log (1 / δ))⌉₊ with hL₀
  have hL₀ge : (5 / 2) * (Real.log n / Real.log (1 / δ)) ≤ L₀ := Nat.le_ceil _
  have h2L : 2 ≤ L₀ := by
    have : (2 : ℝ) ≤ (L₀ : ℝ) := by linarith
    exact_mod_cast this
  have hmn : ⌈δ * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.2 (by nlinarith)
  have hcond : n ^ 2 * (⌈δ * (n : ℝ)⌉₊) ^ L₀ < n ^ L₀ := by
    refine pow_cond δ h0 h1 n hn2 hδn hbig 2 (by norm_num) L₀ ?_
    push_cast
    linarith
  obtain ⟨S, hSsub, hScard, hSno⟩ := exists_card_eq_no_ap hmn h2L hcond
  refine ⟨S, hSsub, ?_, ?_⟩
  · rw [hScard]; exact Nat.le_ceil _
  · intro L hLge a d hd hsub
    exact hSno a d hd ((apF_mono a d (Nat.ceil_le.2 hLge)).trans hsub)
