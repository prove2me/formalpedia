-- Prove2me | Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
-- name    : mme_log_sqrt_loss_eventually_le_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T23:40:54.425748+00:00
-- url     : https://prove2.me/theorems/90dd622f-d22b-4eae-9ca6-82f6abeff6c2
-- title:
--   Fixed logarithmic and square-root losses are absorbed by every positive linear budget
-- statement:
--   Let $a,b,c$ be arbitrary fixed real constants and let $\delta>0$. For all sufficiently large natural numbers $n$,
--
--   $$a\log(n+1)+b\sqrt{n+1}+c\le n\delta.$$
--
--   All logarithms are natural. Signed coefficients are allowed, and no convergence premise is assumed. This analytic lemma turns explicit logarithmic, square-root and constant losses in finite hashing estimates into arbitrarily small linear errors in the directional logarithmic rates.
-- source:
--   Elementary analytic loss-absorption adapter for the finite first-hash bounds in Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp.270–271, https://doi.org/10.1016/S0747-7171(08)80013-2. The proof derives log(n+1)/n→0 and sqrt(n+1)/n→0 from Mathlib's established logarithmic, rational-function and square-root limits; it is not claimed to be a separately numbered assertion of that paper. It consumes no tensor-value or exponent assumption.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

open Filter Topology

set_option autoImplicit false

theorem mme_log_sqrt_loss_eventually_le_linear (a b c delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      a * Real.log ((n : ℝ) + 1) + b * Real.sqrt ((n : ℝ) + 1) + c ≤
        (n : ℝ) * delta := by sorry
