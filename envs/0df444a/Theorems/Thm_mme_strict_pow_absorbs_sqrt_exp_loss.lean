-- Prove2me | Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
-- name    : mme_strict_pow_absorbs_sqrt_exp_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:12:59.709577+00:00
-- url     : https://prove2.me/theorems/559710fd-2f80-4b7f-aefd-a22a939828d1
-- title:
--   A strict exponential base gap absorbs a square-root exponential loss
-- statement:
--   Let $0\le V<B$ and $C\ge0$. Then, for all sufficiently large integers $n$,
--
--   $$
--   V^n \le B^n\exp(-C\sqrt{n+1}).
--   $$
--
--   Thus any strict gap between two exponential bases eventually dominates a subexponential square-root loss. This is the endpoint-safe analytic step used to pass from finite C-tensor extractions with Behrend loss to every strict asymptotic value bound.
-- source:
--   Elementary logarithmic comparison and completion of the square; used in the asymptotic C-tensor value argument of V. Strassen and in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 271--272.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

set_option autoImplicit false

theorem mme_strict_pow_absorbs_sqrt_exp_loss
    (V B C : ℝ) (hV : 0 ≤ V) (hVB : V < B) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      V ^ n ≤ B ^ n *
        Real.exp (-C * Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
  sorry
