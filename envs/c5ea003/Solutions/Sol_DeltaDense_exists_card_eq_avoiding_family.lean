-- Prove2me | solution 1 for DeltaDense.exists_card_eq_avoiding_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:24:57.198671+00:00
-- url     : https://prove2.me/submissions/6c497985-f8fe-4bac-8b56-68fcc1253ae4

-- Sol generated from Bridges/DeltaDenseSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Theorems.Thm_DeltaDense_card_filter_superset
import Theorems.Thm_DeltaDense_choose_ratio
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


/-- Subtracted form of `choose_ratio`: `C(n-L, m-L) · n^L ≤ C(n,m) · m^L`. -/
theorem choose_ratio_sub {L m n : ℕ} (hLm : L ≤ m) (hmn : m ≤ n) :
    (n - L).choose (m - L) * n ^ L ≤ n.choose m * m ^ L := by
  have h := choose_ratio (m - L) (n - L) (by omega) L
  have e1 : n - L + L = n := by omega
  have e2 : m - L + L = m := by omega
  rwa [e1, e2] at h


/-! ## The general first-moment principle -/


/-! ## Progression-free and grid-free dense sets, in integer form -/



/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no long progressions and no progression sumsets -/







open DeltaDense in
theorem solution{ι : Type*} [DecidableEq ι] {n m L : ℕ}
    (I : Finset ι) (W : ι → Finset ℕ) (hW : ∀ i ∈ I, L ≤ (W i).card)
    (hmn : m ≤ n) (hL : 1 ≤ L) (hcond : I.card * m ^ L < n ^ L) :
    ∃ S ⊆ range n, S.card = m ∧ ∀ i ∈ I, ¬ (W i ⊆ S) := by
  classical
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hcond (by rw [zero_pow (by omega : L ≠ 0)]; omega)
    · exact h
  obtain ⟨S₀, hS₀sub, hS₀card⟩ :=
    Finset.exists_subset_card_eq (by simpa using hmn : m ≤ (range n).card)
  by_cases hLm : L ≤ m
  · set Fam : Finset (Finset ℕ) := (range n).powersetCard m with hFam
    have hcardFam : Fam.card = n.choose m := by
      rw [hFam, Finset.card_powersetCard, Finset.card_range]
    set Bad : Finset (Finset ℕ) :=
      I.biUnion (fun i => Fam.filter (fun S => W i ⊆ S)) with hBad
    have hb1 : Bad.card ≤ I.card * ((n - L).choose (m - L)) := by
      refine le_trans (Finset.card_biUnion_le) ?_
      have hterm : ∀ i ∈ I,
          (Fam.filter (fun S => W i ⊆ S)).card ≤ (n - L).choose (m - L) := by
        intro i hi
        by_cases hsub : W i ⊆ range n
        · obtain ⟨P, hPW, hPcard⟩ := Finset.exists_subset_card_eq (hW i hi)
          have hmono : Fam.filter (fun S => W i ⊆ S) ⊆ Fam.filter (fun S => P ⊆ S) := by
            intro S hS
            rw [Finset.mem_filter] at hS ⊢
            exact ⟨hS.1, hPW.trans hS.2⟩
          refine le_trans (Finset.card_le_card hmono) ?_
          rw [hFam, card_filter_superset n m (hPW.trans hsub) (by omega), hPcard]
        · have he : (Fam.filter (fun S => W i ⊆ S)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro S hS hsubS
            rw [hFam, Finset.mem_powersetCard] at hS
            exact hsub (hsubS.trans hS.1)
          simp [he]
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, smul_eq_mul]
    have hchoose_pos : 0 < n.choose m := Nat.choose_pos hmn
    have hb2 : I.card * ((n - L).choose (m - L)) < n.choose m := by
      have h1 := choose_ratio_sub hLm hmn
      have h2 : I.card * ((n - L).choose (m - L)) * n ^ L
          ≤ I.card * (n.choose m * m ^ L) := by
        calc I.card * ((n - L).choose (m - L)) * n ^ L
            = I.card * ((n - L).choose (m - L) * n ^ L) := by ring
          _ ≤ I.card * (n.choose m * m ^ L) := Nat.mul_le_mul_left _ h1
      have h3 : I.card * (n.choose m * m ^ L) < n.choose m * n ^ L := by
        calc I.card * (n.choose m * m ^ L) = n.choose m * (I.card * m ^ L) := by ring
          _ < n.choose m * n ^ L := mul_lt_mul_of_pos_left hcond hchoose_pos
      exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h2 h3)
    have hne : (Fam \ Bad).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.card_sdiff_add_card_inter Fam Bad
      have h2 : (Fam ∩ Bad).card ≤ Bad.card := Finset.card_le_card Finset.inter_subset_right
      omega
    obtain ⟨S, hS⟩ := hne
    rw [Finset.mem_sdiff] at hS
    obtain ⟨hSmem, hSbad⟩ := hS
    have hSmem' : S ⊆ range n ∧ S.card = m := by
      rw [hFam, Finset.mem_powersetCard] at hSmem; exact hSmem
    refine ⟨S, hSmem'.1, hSmem'.2, ?_⟩
    intro i hi hsubS
    exact hSbad (Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_filter.2 ⟨hSmem, hsubS⟩⟩)
  · refine ⟨S₀, hS₀sub, hS₀card, ?_⟩
    intro i hi hsubS
    have h1 := Finset.card_le_card hsubS
    have h2 := hW i hi
    omega
