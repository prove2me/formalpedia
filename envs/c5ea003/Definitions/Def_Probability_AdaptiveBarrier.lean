-- Prove2me | Definitions.Def_Probability_AdaptiveBarrier
-- name    : Probability_AdaptiveBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:22.077615+00:00
-- url     : https://prove2.me/theorems/2fd22f62-efd6-4ef2-a590-5818a6b20710
-- title:
--   Aether Catalog definitions — Probability_AdaptiveBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AdaptiveBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AdaptiveBarrier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
/-
# The Adaptive Barrier (Factoring Lab, Phase A v19c — cycle 2)

Closing **Conjecture 5** of `FUTURE_DIRECTIONS.md`: *the structural-orthogonality
barrier is closed under adaptivity.*

The previous cycle proved that no invariant `g ∘ n` computable from the band
label alone predicts the target better than the band mean
(`FactoringLab.bandMean_is_best_predictor`), and that arbitrary *fixed*
nonlinear aggregation `Φ(w₁, …, w_m)` of finitely many free witnesses stays
`N`-only (`FactoringLab.aggregation_no_better_than_bandMean`).

An obvious escape route is *adaptivity*: run an `N`-only test, and depending on
its outcome run a different test, and so on, finally emitting a candidate
factor.  This file formalizes such a strategy as a finite **decision tree**
whose internal tests and whose leaf outputs are band-measurable, and proves:

* `FactoringLab.DTree.bandMeasurable_eval` — the value computed by such a tree
  is itself band-measurable (structural induction on the tree);
* `FactoringLab.factors_through_band` — every band-measurable function factors
  as `g ∘ n` for some `g : κ → ℝ`;
* `FactoringLab.adaptive_structural_orthogonality` — the output of any such
  tree is orthogonal to the residual `Y − E[Y | n]`;
* `FactoringLab.adaptive_barrier` — no such tree beats the band mean, *for any
  depth and any branching*; the excess error is again exactly the squared
  deviation from the band mean (`adaptive_sq_error_decomposition`);
* `FactoringLab.adaptive_cov_eq_cov_bandMean` and
  `FactoringLab.adaptive_nearEqualN_test` — the near-equal-`N` test applies
  verbatim to adaptive strategies: constant band means force covariance `0`.

Boundary (Stage 4, adversarial review).  The band-measurability hypothesis is
not decorative: `FactoringLab.adaptive_barrier_fails_without_bandMeasurable`
exhibits a two-point population and a depth-`0` tree which attains error `0`
while the band mean has error `1/2`.

Finally `FactoringLab.witnessTree_bandMeasurable` shows the hypothesis is met
by the strategies the framework is about: any tree whose tests are threshold
comparisons of free witnesses `w : κ → ℝ` and whose leaves are `N`-only
invariants is band-measurable, so the barrier covers the whole adaptive
free-witness family.
-/

open Finset

namespace FactoringLab

variable {ι κ : Type*}

/-! ## 1.  Band-measurable functions -/

/-- A function on the population is *band-measurable* when it is constant on
each band: it can be computed from the band label `n i` alone. -/
def BandMeasurable {α : Type*} (Ω : Finset ι) (n : ι → κ) (f : ι → α) : Prop :=
  ∀ i ∈ Ω, ∀ j ∈ Ω, n i = n j → f i = f j





/-! ## 2.  Adaptive strategies as decision trees -/

/-- A finite adaptive strategy: a binary decision tree whose internal nodes
carry a test on the population and whose leaves carry a real-valued output
(the candidate factor). -/
inductive DTree (ι : Type*) where
  | leaf (v : ι → ℝ) : DTree ι
  | node (test : ι → Bool) (l r : DTree ι) : DTree ι

namespace DTree

/-- Running the strategy on a member of the population. -/
def eval : DTree ι → ι → ℝ
  | leaf v, i => v i
  | node t l r, i => if t i then eval l i else eval r i

/-- The number of internal tests: the size of the strategy.  The barrier below
holds uniformly in this quantity — adaptivity of any depth does not help. -/
def size : DTree ι → ℕ
  | leaf _ => 0
  | node _ l r => l.size + r.size + 1

/-- A strategy is `N`-only when every test and every leaf is band-measurable. -/
def BandOnly (Ω : Finset ι) (n : ι → κ) : DTree ι → Prop
  | leaf v => BandMeasurable Ω n v
  | node t l r => BandMeasurable Ω n t ∧ BandOnly Ω n l ∧ BandOnly Ω n r


end DTree


/-! ## 3.  The adaptive barrier -/







/-! ## 4.  The hypothesis is met by adaptive free-witness strategies -/

/-- Pull a strategy expressed in terms of the band label back to the
population. -/
def mapTree (n : ι → κ) : DTree κ → DTree ι
  | DTree.leaf v => DTree.leaf (fun i => v (n i))
  | DTree.node test l r => DTree.node (fun i => test (n i)) (mapTree n l) (mapTree n r)



/-! ## 5.  Boundary: band-measurability cannot be dropped -/


end FactoringLab


