-- Prove2me | solution 1 for DeltaDense.choose_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:58.323404+00:00
-- url     : https://prove2.me/submissions/f28264af-f6c4-425e-8f39-b5ea6bb9c620

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
theorem solution(m n : ℕ) (hmn : m ≤ n) :
    ∀ L : ℕ, n.choose m * (n + L) ^ L ≤ (n + L).choose (m + L) * (m + L) ^ L := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rcases Nat.eq_zero_or_pos (n + L) with h0 | hpos
    · have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      subst hn; subst hm; simp
    · have key : (n + L + 1) * (n + L).choose (m + L)
          = (n + L + 1).choose (m + L + 1) * (m + L + 1) := Nat.add_one_mul_choose_eq _ _
      have hstep : (m + L) * (n + L + 1) ≤ (m + L + 1) * (n + L) := by nlinarith [hmn]
      have h1 : n.choose m * (n + L) ^ L * (n + L + 1) ^ L
          ≤ (n + L).choose (m + L) * (m + L) ^ L * (n + L + 1) ^ L :=
        Nat.mul_le_mul_right _ ih
      have h2 : ((m + L) * (n + L + 1)) ^ L ≤ ((m + L + 1) * (n + L)) ^ L :=
        Nat.pow_le_pow_left hstep L
      have h3 : n.choose m * (n + L + 1) ^ L * (n + L) ^ L
          ≤ (n + L).choose (m + L) * (m + L + 1) ^ L * (n + L) ^ L := by
        calc n.choose m * (n + L + 1) ^ L * (n + L) ^ L
            = n.choose m * (n + L) ^ L * (n + L + 1) ^ L := by ring
          _ ≤ (n + L).choose (m + L) * (m + L) ^ L * (n + L + 1) ^ L := h1
          _ = (n + L).choose (m + L) * ((m + L) * (n + L + 1)) ^ L := by rw [mul_pow]; ring
          _ ≤ (n + L).choose (m + L) * ((m + L + 1) * (n + L)) ^ L :=
              Nat.mul_le_mul_left _ h2
          _ = (n + L).choose (m + L) * (m + L + 1) ^ L * (n + L) ^ L := by rw [mul_pow]; ring
      have h4 : n.choose m * (n + L + 1) ^ L
          ≤ (n + L).choose (m + L) * (m + L + 1) ^ L :=
        Nat.le_of_mul_le_mul_right h3 (Nat.pow_pos hpos)
      calc n.choose m * (n + (L + 1)) ^ (L + 1)
          = (n + L + 1) * (n.choose m * (n + L + 1) ^ L) := by ring_nf
        _ ≤ (n + L + 1) * ((n + L).choose (m + L) * (m + L + 1) ^ L) :=
            Nat.mul_le_mul_left _ h4
        _ = ((n + L + 1) * (n + L).choose (m + L)) * (m + L + 1) ^ L := by ring
        _ = ((n + L + 1).choose (m + L + 1) * (m + L + 1)) * (m + L + 1) ^ L := by rw [key]
        _ = (n + (L + 1)).choose (m + (L + 1)) * (m + (L + 1)) ^ (L + 1) := by ring_nf
