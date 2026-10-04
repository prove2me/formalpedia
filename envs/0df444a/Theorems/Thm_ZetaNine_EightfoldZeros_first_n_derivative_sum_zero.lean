-- Prove2me | Theorems.Thm_ZetaNine_EightfoldZeros_first_n_derivative_sum_zero
-- name    : ZetaNine.EightfoldZeros.first_n_derivative_sum_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:34:29.909568+00:00
-- url     : https://prove2.me/theorems/e5bcddcb-3925-4391-91fe-bc8e6284a6ec
-- title:
--   Eightfold zeros eliminate the first n derivative terms
-- statement:
--   For the explicit repaired function $R_n^*$, every integer derivative order $0\le r<8$ satisfies
--
--   $$\sum_{j=1}^{n}(R_n^*)^{(r)}(j)=0.$$
--
--   This holds for every natural $n$, including the empty sum at $n=0$. The derivatives are genuine iterated real derivatives of the rational function. In particular the first $n$ leakage terms of the seventh-derivative series vanish exactly. The theorem does not assert convergence, eventual nonvanishing, decay or irrationality.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/new-linear-form-route-repair-2026-10-02.md, opening unnumbered definition of R*_n and the following endpoint-zero paragraph.

import Definitions.Def_ZetaNine_EightfoldZeros
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
open scoped BigOperators
open ZetaNine.EightfoldZeros

theorem ZetaNine.EightfoldZeros.first_n_derivative_sum_zero (n r : ℕ) (hr : r < 8) :
    (∑ k ∈ Finset.range n, iteratedDeriv r (repairFunction n) ((k + 1 : ℕ) : ℝ)) = 0 := by sorry
