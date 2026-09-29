-- Prove2me | Theorems.Thm_DeltaDense_exists_card_eq_avoiding_family
-- name    : DeltaDense.exists_card_eq_avoiding_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:18.732098+00:00
-- url     : https://prove2.me/theorems/14cb8c15-e154-4503-a9f1-fbd3cd968b0f
-- title:
--   First-moment principle.
-- statement:
--   **First-moment principle.**  Let `W : ι → Finset ℕ` be a family of sets indexed by a
--   finite set `I`, each of size at least `L ≥ 1`.  If `|I| · m^L < n^L` and `m ≤ n`, then
--   some `m`-element subset `S ⊆ [n]` contains none of the sets `W i`, `i ∈ I`.
--
--   This is the counting form of the probabilistic statement that a uniformly random
--   `m`-subset of `[n]` contains a fixed `L`-set with probability at most `(m/n)^L`.
--
--   ```lean
--   theorem DeltaDense.exists_card_eq_avoiding_family{ι : Type*} [DecidableEq ι] {n m L : ℕ}
--       (I : Finset ι) (W : ι → Finset ℕ) (hW : ∀ i ∈ I, L ≤ (W i).card)
--       (hmn : m ≤ n) (hL : 1 ≤ L) (hcond : I.card * m ^ L < n ^ L) :
--       ∃ S ⊆ range n, S.card = m ∧ ∀ i ∈ I, ¬ (W i ⊆ S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/DeltaDenseSumsetAvoidance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/DeltaDenseSumsetAvoidance.lean#L208

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

theorem DeltaDense.exists_card_eq_avoiding_family{ι : Type*} [DecidableEq ι] {n m L : ℕ}
    (I : Finset ι) (W : ι → Finset ℕ) (hW : ∀ i ∈ I, L ≤ (W i).card)
    (hmn : m ≤ n) (hL : 1 ≤ L) (hcond : I.card * m ^ L < n ^ L) :
    ∃ S ⊆ range n, S.card = m ∧ ∀ i ∈ I, ¬ (W i ⊆ S) := by sorry
