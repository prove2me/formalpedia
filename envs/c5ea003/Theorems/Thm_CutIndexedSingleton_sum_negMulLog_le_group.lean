-- Prove2me | Theorems.Thm_CutIndexedSingleton_sum_negMulLog_le_group
-- name    : CutIndexedSingleton.sum_negMulLog_le_group
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:23:42.781527+00:00
-- url     : https://prove2.me/theorems/b22b536f-785b-42d7-a120-d810112d63cb
-- title:
--   Grouping inequality.
-- statement:
--   **Grouping inequality.**  For a nonnegative weight vector on a set of at most
--   `N` indices, the entropy of the weights is at most the entropy of their sum plus
--   `(total weight) · log N`.
--
--   ```lean
--   theorem CutIndexedSingleton.sum_negMulLog_le_group{ι : Type*} (F : Finset ι) (p : ι → ℝ)
--       (hp : ∀ i ∈ F, 0 ≤ p i) {N : ℕ} (hN : F.card ≤ N) (hN0 : 0 < N) :
--       ∑ i ∈ F, Real.negMulLog (p i)
--         ≤ Real.negMulLog (∑ i ∈ F, p i) + (∑ i ∈ F, p i) * Real.log N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CutIndexedEntropicSingleton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CutIndexedEntropicSingleton.lean#L67

-- Thm stub generated from Novelty/CutIndexedEntropicSingleton.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropicSingleton
import Definitions.Def_Novelty_CutIndexedEntropyMono

/-!
# Cut-indexed defects VI: the entropic cut-wise Singleton inequality

File I proved the *counting* cut-wise Singleton inequality
`|C| ≤ q ^ (k - |S|) * cutRank C S`.  File V showed that the entropy profile
`S ↦ cutEntropy C S` is monotone.  This file completes the entropic mirror of the
`CutData` axioms by proving the missing **chain-rule bound**
`H(T) ≤ H(S) + (|T| - |S|) log q`, and deduces the sharpest form of the theory:

`log |C| ≤ H(S) + (k - |S|) log q` for every cut with `|S| ≤ k = n + 1 - d`.

Because `H(S) ≤ log (cutRank C S)` always, this **implies** the counting cut-wise
Singleton inequality and is strictly stronger whenever the marginal on `S` is not
uniform.

## Main results

* `sum_negMulLog_le_group` : the *log-sum / grouping* inequality
  `∑_{i ∈ F} negMulLog pᵢ ≤ negMulLog (∑ pᵢ) + (∑ pᵢ) log N` for `|F| ≤ N`;
* `card_fiber_restrictCut_le` : a pattern on `S` has at most `q ^ (|T| - |S|)`
  extensions to `T`;
* `cutEntropy_le_add_of_subset` : **the entropic one-block growth bound**
  `H(T) ≤ H(S) + (|T| - |S|) log q`;
* `cutEntropy_eq_log_card_of_resolving` : above the Singleton dimension the cut
  entropy is exactly `log |C|`;
* `entropic_cutwise_singleton` : **the entropic cut-wise Singleton inequality**;
* `entropic_cutwise_singleton_implies_counting` : it implies the counting version
  of file I;
* `entropicDefect_nonneg`, `entropicDefect_eq_zero_iff_isMDS` : the entropic cut
  defect is nonnegative, and at the empty cut it vanishes exactly for MDS codes.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 2): every axiom of `CutData` should have an
entropic mirror, and the mirrored Singleton argument should be *strictly sharper*
than the counting one, because entropy sees the shape of the fibre distribution
and rank only sees its support.

Experiment (Experimenter): the mirror is complete.  The one-block growth bound is
the grouping inequality applied fibre-by-fibre, with `N = q ^ (|T| - |S|)` the
number of extensions of a pattern; the proof of the grouping inequality is the
same `log x ≤ x - 1` estimate that powers
`IITTensorNetwork.sum_negMulLog_le_log_card_support`, but *relativised* to a
sub-block, which is what makes it usable inside a sum over cuts.

Analysis (Analyst): the entropic inequality is strictly stronger: for the code
`{000, 100, 010, 110, 001}` of `Examples.pentaCode` the counting bound at
`S = {0}` is not tight while the entropic one records the exact non-uniformity of
the fibres.  The mirror also explains file III: the quantum inequality is a third
member of the same family, with `log (Schmidt rank)` in place of `H(S)`, and it is
the only one of the three that can *fail* to saturate for MDS codes, because of
purity on the complement.

Critique (Critic): the equality analysis at the empty cut needs `2 ≤ q` (for
`q = 1` all logarithms vanish and the criterion is vacuous) and `C.Nonempty`;
`entropicDefect_eq_zero_iff_isMDS` records both.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}

/-! ## The grouping (log-sum) inequality -/

theorem CutIndexedSingleton.sum_negMulLog_le_group{ι : Type*} (F : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ F, 0 ≤ p i) {N : ℕ} (hN : F.card ≤ N) (hN0 : 0 < N) :
    ∑ i ∈ F, Real.negMulLog (p i)
      ≤ Real.negMulLog (∑ i ∈ F, p i) + (∑ i ∈ F, p i) * Real.log N := by sorry
