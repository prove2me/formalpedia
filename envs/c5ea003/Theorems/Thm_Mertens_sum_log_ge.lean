-- Prove2me | Theorems.Thm_Mertens_sum_log_ge
-- name    : Mertens.sum_log_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:25:59.579281+00:00
-- url     : https://prove2.me/theorems/28ab0ce9-bb34-4b0c-a22d-51f83c061026
-- title:
--   Explicit Stirling-type lower bound $\sum_{n \le x} \log n \ge x\log x - 2x$
-- statement:
--   For a real number $x \ge 1$, consider the sum of logarithms over the integers $n$ with $0 < n \le \lfloor x \rfloor$ (equivalently, $\log \lfloor x \rfloor!$).
--
--   **Statement.** For every real $x \ge 1$,
--   $$\sum_{1 \le n \le \lfloor x \rfloor} \log n \;\ge\; x \log x - 2x.$$
--
--   This is an explicit weak Stirling bound with the concrete constant $2$ in place of an $O(x)$ error. In the module `Zeta23.FromPNTPlus.Mertens` it is the main analytic input to the lower bound `Mertens.E1Lambda.ge` for the remainder in Mertens' first theorem, via the hyperbola-method identity $\sum_{n \le x} \log n = \sum_{d \le x} \Lambda(d) \lfloor x/d \rfloor$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/Mertens.lean#L104-L131

import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens

open Mertens
open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log

theorem Mertens.sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by sorry
