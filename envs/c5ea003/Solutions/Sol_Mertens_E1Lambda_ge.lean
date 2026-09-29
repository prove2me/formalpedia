-- Prove2me | solution 1 for Mertens.E1Lambda.ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:53:54.253778+00:00
-- url     : https://prove2.me/submissions/b0feafa8-51d8-4c37-9946-43c8aa223009

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
import Theorems.Thm_Mertens_sum_log_ge

-- from Zeta23.FromPNTPlus.Mertens
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mertens.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Original authors per that project's blueprint (Euler–Maclaurin and Mertens
sections drawn from Leo Goldmakher, "A quick proof of Mertens' theorem",
https://web.williams.edu/Mathematics/lg5/mertens.pdf).

Declarations ported (source lines 1–371):
  Mertens.sum_Ioc_one_eq_sum_Ioc_zero, Mertens.sum_log_eq, Mertens.sum_log_le,
  Mertens.integral_log_le, Mertens.sum_log_ge, Mertens.sum_log_eq_log_factorial,
  Mertens.sum_log_eq_sum_mangoldt, Mertens.E₁Λ, Mertens.sum_mangoldt_div_eq,
  Mertens.E1Lambda.ge, Mertens.E1Lambda.le, Mertens.sum_mangoldt_div_eq_log,
  Mertens.E₁Λ.bounded'.

Local modifications:
  * the source's `section EulerMaclaurin` (B1 ... sum_eq_integral_add_integral_deriv)
    now lives in Zeta23/FromPNTPlus/EulerMaclaurin.lean (re-ported from upstream
    v4.32.2, where that section was split out of Mertens.lean into its own file),
    imported here;
  * dropped `import Architect` and all `@[blueprint ...]` attributes and
    `blueprint_comment` blocks (blueprint tooling we do not vendor); statement
    text retained as plain docstrings on the main theorems;
  * dropped three root-level helpers unused by the ported region (each is
    referenced only past our truncation point): Filter.EventuallyEq.iff_eventually,
    Real.inv_log_eq_o_one, Real.one_eq_o_log_log — nothing is injected into the
    Real or Filter namespaces by this file;
  * dropped a stray `#check ArithmeticFunction.vonMangoldt_sum`;
  * truncated after E₁Λ.bounded' (everything later — the sorry'd E₁Λ.bounded,
    the prime-form/second/third theorems — is not ported; no sorry enters);
  * added the closing `end Mertens`.
Modified 2026 by Anthropic PBC.
-/




namespace Mertens


open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log









/-- For any `x`, `∑ n ≤ x, log n = ∑ d ≤ x, Λ(d) ⌊x/d⌋`. -/
theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]








end Mertens
open Mertens
open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log

theorem solution {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr with d _
    · exact vonMangoldt_nonneg
    · exact Nat.floor_le <| div_nonneg (by linarith : (0:ℝ) ≤ x) (Nat.cast_nonneg d)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring
