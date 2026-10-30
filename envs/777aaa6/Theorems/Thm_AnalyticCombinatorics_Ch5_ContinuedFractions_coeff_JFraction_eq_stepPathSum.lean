-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_ContinuedFractions_coeff_JFraction_eq_stepPathSum
-- name    : AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_eq_stepPathSum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:29:06.741718+00:00
-- url     : https://prove2.me/theorems/ea8d61a6-136f-4f5c-92f5-36f55e0536d2
-- title:
--   Finite J-fraction coefficients enumerate bounded weighted Motzkin step paths
-- statement:
--   Let $R$ be a commutative ring, let $h,n\in\mathbb N$, and let $a,b,c:\mathbb N\to R$ be arbitrary weight families. For a family $u$, put $(\sigma u)(k)=u(k+1)$. Define formal series $J_h(a,b,c)\in R[[z]]$ by
--
--   $$J_0(a,b,c)=\frac{1}{1-c(0)z},\qquad
--   J_{h+1}(a,b,c)=\frac{1}{1-c(0)z-a(0)b(0)z^2J_h(\sigma a,\sigma b,\sigma c)}.$$
--
--   The reciprocals are formal inverses of series with constant coefficient $1$. Let $\mathcal M_{h,n}$ consist of all length-$n$ lists of up, down and level steps that start at height $0$, finish at height $0$, and stay at heights $0,\ldots,h$. Give an up step from $k$ to $k+1$ weight $a(k)$, a down step from $k+1$ to $k$ weight $b(k)$, and a level step at $k$ weight $c(k)$. Let $w(p)$ be the product of its step weights, with empty product $1$. Then
--
--   $$[z^n]J_h(a,b,c)=\sum_{p\in\mathcal M_{h,n}}w(p).$$
--
--   The height ceiling $h$ is finite and fixed in this identity; $h=0$ and $n=0$ are included. No positivity or analytic convergence assumption is required.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/ContinuedFractions/FlajoletStepPath.lean#L289. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_FlajoletStepPath
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

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.ContinuedFractions

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

theorem AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_eq_stepPathSum (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = ∑ p ∈ closedMotzkinFinset h n, stepWeight a b c 0 p := by sorry
