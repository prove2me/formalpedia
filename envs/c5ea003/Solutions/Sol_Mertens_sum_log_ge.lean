-- Prove2me | solution 1 for Mertens.sum_log_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:54:49.079197+00:00
-- url     : https://prove2.me/submissions/77cb2a7e-896a-4988-88e3-22cc2e983c77

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





lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]












end Mertens
open Mertens
open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log

theorem solution {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]
