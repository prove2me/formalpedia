-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_FlajoletStepPath
-- name    : AnalyticCombinatorics_Ch5_ContinuedFractions_FlajoletStepPath
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:27:01.007445+00:00
-- url     : https://prove2.me/theorems/91d85eef-8354-497a-a199-049dac2ce1f7
-- title:
--   The finite set of bounded closed Motzkin step lists
-- statement:
--   closedMotzkinFinset h n is the finite image of all first-return path codes under toSteps. Its separate membership theorem characterizes precisely the lists satisfying ClosedMotzkin h n. The definition retains arbitrary natural height h and length n; no unrestricted-height limit is taken.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/ContinuedFractions/FlajoletStepPath.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_FlajoletPathBijection
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch5 §V — Flajolet's theorem on genuine step-list lattice paths (the bijection)

This completes the faithfulness upgrade begun in `FlajoletPathBijection.lean`: it proves the
weight-preserving bijection between the first-return-coded `MotzkinPath` type and genuine
lattice paths (`List Step` with the `Walk`/`ClosedMotzkin` validity), and assembles the capstone.

* `Walk_split` — drop a valid prefix (converse of `Walk_append`).
* `toSteps_surjective` — every closed lattice path is `toSteps` of some first-return code
  (the parse, via `first_passage` — the cycle lemma).
* `balanced_split_eq` — first-return uniqueness (two balanced prefixes + `down` agree).
* `toSteps_injective` — distinct codes give distinct step lists.
* `coeff_JFraction_eq_stepPathSum` — **Flajolet's theorem on real lattice paths**: the `z^n`
  coefficient of the bounded J-fraction is the weighted sum over all height-`≤h`, length-`n`
  closed Motzkin step paths, with the first-return decomposition now a *theorem*, not a definition.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

/-- The genuine lattice-path finset: images of the codes under `toSteps`. -/
def closedMotzkinFinset (h n : ℕ) : Finset (List Step) :=
  (Finset.univ : Finset (MotzkinPath h n)).image (toSteps h n)

end

end AnalyticCombinatorics.Ch5.ContinuedFractions


