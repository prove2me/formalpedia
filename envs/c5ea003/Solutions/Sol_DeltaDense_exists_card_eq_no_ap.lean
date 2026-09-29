-- Prove2me | solution 1 for DeltaDense.exists_card_eq_no_ap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:30:25.265948+00:00
-- url     : https://prove2.me/submissions/641a4a41-0543-46ae-8a52-8d20304d3f60

-- Sol generated from Bridges/DeltaDenseSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Theorems.Thm_DeltaDense_exists_card_eq_avoiding_family
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


lemma mem_apF {a d L x : ℕ} : x ∈ apF a d L ↔ ∃ i < L, a + d * i = x := by
  simp [apF]

/-- A progression with positive common difference has exactly `L` terms. -/
lemma card_apF (a : ℕ) {d : ℕ} (hd : 0 < d) (L : ℕ) : (apF a d L).card = L := by
  rw [apF, Finset.card_image_of_injective _ (by intro i j hij; simp at hij; omega),
    Finset.card_range]


lemma self_mem_apF {a d L : ℕ} (hL : 0 < L) : a ∈ apF a d L :=
  mem_apF.2 ⟨0, hL, by ring⟩

lemma second_mem_apF {a d L : ℕ} (hL : 1 < L) : a + d ∈ apF a d L :=
  mem_apF.2 ⟨1, hL, by ring⟩




/-! ## The counting estimates -/




/-! ## The general first-moment principle -/


/-! ## Progression-free and grid-free dense sets, in integer form -/



/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no long progressions and no progression sumsets -/







open DeltaDense in
theorem solution{n m L : ℕ} (hmn : m ≤ n) (hL : 2 ≤ L)
    (hcond : n ^ 2 * m ^ L < n ^ L) :
    ∃ S ⊆ range n, S.card = m ∧ ∀ a d : ℕ, 0 < d → ¬ (apF a d L ⊆ S) := by
  classical
  set I : Finset (ℕ × ℕ) := (range n) ×ˢ (Icc 1 n) with hI
  have hIcard : I.card = n ^ 2 := by
    rw [hI, Finset.card_product, Finset.card_range, Nat.card_Icc]
    simp [sq]
  obtain ⟨S, hSsub, hScard, hSno⟩ :=
    exists_card_eq_avoiding_family I (fun p => apF p.1 p.2 L)
      (fun p hp => by
        rw [hI, Finset.mem_product, Finset.mem_Icc] at hp
        rw [card_apF _ (by omega : 0 < p.2)])
      hmn (by omega) (by rw [hIcard]; exact hcond)
  refine ⟨S, hSsub, hScard, ?_⟩
  intro a d hd hsub
  have ha : a < n := by simpa using hSsub (hsub (self_mem_apF (by omega)))
  have had : a + d < n := by simpa using hSsub (hsub (second_mem_apF (by omega)))
  exact hSno (a, d) (by rw [hI, Finset.mem_product, Finset.mem_Icc]; exact ⟨by simpa using ha,
    hd, by omega⟩) hsub
