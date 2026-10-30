-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch7_SingularityApp_fussCatalan_four_isEquivalent
-- name    : AnalyticCombinatorics.Ch7.SingularityApp.fussCatalan_four_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T19:09:26.484584+00:00
-- url     : https://prove2.me/theorems/06346e83-0b31-4619-8553-1da8e2c89e2a
-- title:
--   The arity-four Fuss–Catalan specialization
-- statement:
--   For the literal source sequence $F_{4,n}$, with $F_{p,n}=\binom{pn}{n}/((p-1)n+1)$ and the source constants $C_4=\texttt{fussCatalanConst}(4)$ and $B_4=\texttt{fussCatalanBase}(4)$, $$F_{4,n}\sim C_4 B_4^n n^{-3/2}.$$ This selected result represents the source specialization module; its arity-five and arity-six corollaries are not automatically selected.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/FussCatalanInstances.lean#L22. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalan
import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Named Fuss–Catalan instances (p-ary trees), F&S Ch VII

Concrete specializations of `fussCatalan_isEquivalent` to the classical small `p`-ary tree families:
ternary already lives in `TernaryTrees`; here we record quaternary (`p = 4`), quinary (`p = 5`) and
senary (`p = 6`), with their explicit growth bases `p^p/(p-1)^(p-1)`.

Each asymptotic is an immediate instance of the general theorem; the growth-base values are by
`norm_num`. (Opus-authored increment; no codex.)
-/

open Filter Asymptotics

theorem AnalyticCombinatorics.Ch7.SingularityApp.fussCatalan_four_isEquivalent :
    (fun n : ℕ => (_root_.fussCatalan 4 n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        _root_.fussCatalanConst 4 * _root_.fussCatalanBase 4 ^ n *
          ((n : ℝ) ^ (-(3 / 2) : ℝ))) := by sorry
