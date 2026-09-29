-- Prove2me | Theorems.Thm_TFoldSumsetAvoidance_sumsetList_card_lower
-- name    : TFoldSumsetAvoidance.sumsetList_card_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:45:21.060374+00:00
-- url     : https://prove2.me/theorems/0b42bd33-4281-41ec-94c6-ecba3781a322
-- title:
--   Sharp iterated Cauchy–Davenport bound.
-- statement:
--   **Sharp iterated Cauchy–Davenport bound.** For a list of nonempty finite
--   integer sets, the size of the `t`-fold sumset satisfies
--   `(Σ |Aᵢ|) + 1 ≤ |A₁ + ⋯ + A_t| + t`, equivalently
--   `|A₁ + ⋯ + A_t| ≥ (Σ|Aᵢ|) - (t-1)`. The bound is saturated by arithmetic
--   progressions.
--
--   ```lean
--   theorem TFoldSumsetAvoidance.sumsetList_card_lower(l : List (Finset ℤ)) (h : ∀ A ∈ l, A.Nonempty) :
--       (l.map Finset.card).sum + 1 ≤ (sumsetList l).card + l.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TFoldSumsetAvoidance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TFoldSumsetAvoidance.lean#L106

-- Thm stub generated from Logic/PosetTheory/TFoldSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TFoldSumsetAvoidance
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avoidance of `t`-fold sumsets in dense sets: the sumset-growth backbone

Fix an integer `t ≥ 2`. A finite set `S` of integers is said to *contain* the
`t`-fold sumset `A₁ + ⋯ + A_t` when every sum `a₁ + ⋯ + a_t` with `aᵢ ∈ Aᵢ`
lies in `S`. A recurring theme in additive combinatorics is that a set which is
*too small* cannot contain the sumset of `t` large sets: growth of iterated
sumsets is unavoidable.

This file develops the exact, sharp growth backbone for iterated sumsets of
integers and turns it into a family of clean **avoidance theorems**.

## Main results

* `sumsetList_card_lower` — the sharp iterated Cauchy–Davenport bound: for a
  list `l` of nonempty finite integer sets,
  `(Σ |Aᵢ|) + 1 ≤ |A₁ + ⋯ + A_t| + t`, i.e. `|A₁ + ⋯ + A_t| ≥ (Σ|Aᵢ|) - (t-1)`.

* `sumsetList_card_uniform` — the uniform specialisation: if there are `t` parts
  each of size at least `k`, then `|A₁ + ⋯ + A_t| ≥ t(k-1) + 1`.

* `sumset_containment_forces_card` — **necessary condition for containment.**
  If `S` contains a `t`-fold sumset whose parts all have size `≥ k`, then
  `|S| ≥ t(k-1) + 1`. Growth of the sumset is forced by the sizes of the parts.

* `sumset_avoidance` — **the avoidance principle (contrapositive).** Any set `S`
  with `|S| ≤ t(k-1)` avoids *every* `t`-fold sumset whose parts all have size
  `≥ k`.

* `dense_set_avoids_large_sumsets` — **dense avoidance existence.** For every
  ambient size `n`, density `δ ≤ 1`, part count `t` and threshold `k` with
  `n ≤ t(k-1)`, there is a set `S` inside `{0, …, n-1}` of density at least `δ`
  which contains no `t`-fold sumset with all parts of size `≥ k`.

The deterministic threshold obtained here is *linear*, of the shape
`k ≳ n / t`. The celebrated probabilistic phenomenon — that a set of density `δ`
can already avoid `t`-fold sumsets once the parts merely exceed
`(log n / log(1/δ))^{1/(t-1)}` — lives far below this linear barrier and is
recorded as the leading open direction of the study.

## Tags
sumset, Cauchy–Davenport, additive combinatorics, sumset avoidance, iterated sumset

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).** Iterated sumsets of `t` integer sets must grow:
a set `S` containing `A₁ + ⋯ + A_t` should be forced to be large whenever the
parts `Aᵢ` are large. Conjectured sharp form: `|A₁+⋯+A_t| ≥ (Σ|Aᵢ|) - (t-1)`,
generalising the single Cauchy–Davenport step `|A+B| ≥ |A|+|B|-1` over a
torsion-free group.

**Experiment (Experimenter).** We modelled the `t`-fold sumset as a right fold
`foldr (· + ·) {0}` over a list of finite sets and proved the sharp bound by
induction, feeding each `cons` step through the single-step Cauchy–Davenport
inequality for torsion-free groups. The uniform corollary and the containment /
avoidance statements then follow by pure arithmetic (`omega`). Concrete check:
`{0,1} + {0,10} = {0,1,10,11}`, size `4 = (2+2) - 1`, saturating the bound.

**Analysis (Analyst).** The linear growth backbone is *true and sharp*
(arithmetic progressions saturate it). It yields a deterministic avoidance
threshold of order `n/t`. Attempts to push the threshold down to the
probabilistic `(log n)^{1/(t-1)}` scale via a naive union bound over all `t`-tuples
of `k`-sets *fail*: the count `n^{tk}` of tuples overwhelms the containment
probability `δ^{t(k-1)+1}` unless `n ≲ 1/δ`. This confirms that the deep result
genuinely needs the structural, non-linear counting of the source paper — it is
"true but hard", not reachable from the growth backbone alone.

**Critique (Critic).** None of the exported theorems are vacuous: each is
witnessed by explicit saturating examples (arithmetic progressions), and the
existence theorem produces a set of density `≥ δ`. The proofs use genuine
induction and the Cauchy–Davenport inequality, not `decide`/`simp`-only. The one
honesty caveat — the linear vs. logarithmic threshold gap — is documented in the
statement docstrings and carried into `FUTURE_DIRECTIONS.md`.

**Synthesis (Principal Investigator).** The sharp iterated Cauchy–Davenport
bound is the correct, reusable foundation on which any quantitative sumset
avoidance theory must sit. It cleanly delivers a deterministic avoidance regime
and isolates the precise place where the probabilistic method is indispensable.
-/

open Finset Pointwise

open TFoldSumsetAvoidance

theorem TFoldSumsetAvoidance.sumsetList_card_lower(l : List (Finset ℤ)) (h : ∀ A ∈ l, A.Nonempty) :
    (l.map Finset.card).sum + 1 ≤ (sumsetList l).card + l.length := by sorry
