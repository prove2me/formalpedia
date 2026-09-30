-- Prove2me | Theorems.Thm_moebius_holomorphic_extension_unique_and_normalized
-- name    : moebius_holomorphic_extension_unique_and_normalized
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:45:48.621046+00:00
-- url     : https://prove2.me/theorems/bf8ed0d7-44cc-4185-8c14-5f6f459e5a19
-- title:
--   Uniqueness and normalization of a holomorphic Moebius extension
-- statement:
--   Suppose $F$ and $G$ are holomorphic on $H=\{s\in\mathbb C:\operatorname{Re}s>1/2\}$ and both agree with $\sum_{n\ge1}\mu(n)n^{-s}$ for $\operatorname{Re}s>1$. Then
--
--   $$F|_H=G|_H,\qquad F(1)=0,\qquad F'(1)=1.$$
--
--   This determines both the continuation on its domain and its normalization at the pole of zeta. Values outside $H$ are unconstrained. The theorem does not assert that such extensions exist.
-- source:
--   Derived corollary of the analytic identity theorem and zeta's residue one at s=1. Pinned Mathlib: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Uniqueness.lean#L223, AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L242, riemannZeta_residue_one. The concrete regularization proof uses https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L77, Complex.Gammaℝ_one.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open MeasureTheory
open scoped Topology

theorem moebius_holomorphic_extension_unique_and_normalized
    (F G : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re})
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hmatchF : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s)
    (hmatchG : ∀ s : ℂ, 1 < s.re →
      G s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s) :
    Set.EqOn F G {s : ℂ | 1 / 2 < s.re} ∧ F 1 = 0 ∧ HasDerivAt F 1 1 := by sorry
