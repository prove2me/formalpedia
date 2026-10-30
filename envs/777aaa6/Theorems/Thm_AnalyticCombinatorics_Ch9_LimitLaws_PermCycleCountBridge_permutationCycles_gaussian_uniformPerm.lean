-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_PermCycleCountBridge_permutationCycles_gaussian_uniformPerm
-- name    : AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.permutationCycles_gaussian_uniformPerm
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:57:56.929725+00:00
-- url     : https://prove2.me/theorems/4f44f372-4dd4-4f0c-8f49-d4c552526db3
-- title:
--   Gaussian fluctuations of cycles in a genuine uniform permutation
-- statement:
--   Let $\sigma_n$ be uniformly distributed on all permutations of $\{0,\ldots,n-1\}$, let $K_n$ count all its cycles including fixed points, and let $H_n=\sum_{j=1}^n1/j$. Then $$\frac{K_n-H_n}{\sqrt{H_n}}\ \Longrightarrow\ N(0,1).$$ The probability carrier is `Equiv.Perm (Fin n)` with its own uniform measure at each n; the limit is the identity variable on a separate real Gaussian space. No common source space is imposed.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/PermCycleCountBridge.lean#L576. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PermutationCycles
import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_ExpectedCycles
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Towards the Feller → uniform-permutation cycle-count bridge

The Gaussian cycle CLT proved in `PermutationCycles.lean`
(`permutationCycles_tendstoInDistribution_gaussian`) is stated for the **Feller
coupling** `cycleP n = Measure.pi (Bernoulli(1/(k+1)))`, NOT for the genuine
uniform permutation measure `uniformPermMeasure n`.  To upgrade the result to a
*faithful* statement about uniform random permutations one needs the
**equidistribution bridge**: the total cycle count of a uniform random
permutation of `Fin n` has the same law (on `ℕ`) as `∑_{k=1}^n Bern(1/k)`.

Both laws have the same probability generating function

  `E[x^{Ncyc}] = ∏_{k=1}^n (x + k - 1)/k = x^{(n)} / n!`   (rising factorial / n!),

so equality of laws follows from the **rising-factorial cycle-count identity**

  `∑_{σ : Perm (Fin n)} x^{Ncyc(σ)} = ∏_{k=0}^{n-1} (x + k)`.

This file banks the *verified foundation* for that identity: the behaviour of the
number-of-cycles statistic `numC` under the `Equiv.Perm.decomposeOption`
bijection `Perm (Option α) ≃ Option α × Perm α`, which is the inductive engine of
the rising-factorial identity.  The "none-fixed" half of the recursion is proved
here in full (clean-3).  The remaining "splice/merge" half — and the assembly
into the generating identity, the char-function computation, and the
`IdentDistrib` transport of the Gaussian CLT — is documented as the open content.

`numC σ` is the genuine number of orbits (cycles, including fixed points) of `σ`:
`numC σ = (#α - #support σ) + (#nontrivial cycles of σ)`
        = (number of fixed points) + (number of nontrivial cycles).
-/

open Equiv Equiv.Perm

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch9
open AnalyticCombinatorics.Ch9.LimitLaws

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## The equidistribution bridge and the faithful uniform-permutation Gaussian CLT

We now finish the tail.  The remaining steps are purely the standard assembly:

1. compute the characteristic function of the law of `totalCycleCount` under
   `uniformPermMeasure` from the rising-factorial identity `cycleGen_fin`;
2. match it to the Feller `cycleCount_charFun`;
3. conclude `IdentDistrib` on `ℝ` via `Measure.ext_of_charFun`;
4. transport the banked Feller Gaussian CLT across the `IdentDistrib`.
-/

open MeasureTheory ProbabilityTheory Complex Filter

theorem AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.permutationCycles_gaussian_uniformPerm :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n (σ : Equiv.Perm (Fin n)) =>
        ((RCyclesPoissonNS.totalCycleCount n σ : ℝ) - cycleH n) / Real.sqrt (cycleH n))
      atTop (fun x : ℝ => x) RCyclesPoissonNS.uniformPermMeasure (gaussianReal 0 1) := by sorry
