-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.approximationExponentUpper_of_quadratic_forms
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:17:32.23122+00:00
-- url     : https://prove2.me/submissions/2ff0ec59-a2c1-43a6-97f6-f1abe8ba532c

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_separation_of_exponential_envelope
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_QuadLogRate_exp_lower
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_QuadLogRate_exp_upper
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_eventually_linear_le_square
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace PaperR9
end PaperR9

/-!
# A complete quadratic-mesh irrationality-measure consumer

The conclusion is uniform over all integer numerators
and all sufficiently large positive denominators. No independence assumption
on successive coefficient pairs is used. The actual 2004 source construction
is NOT asserted by this module.
-/

namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped Topology
open PaperR9





/-- A positive quadratic crosses every fixed real level. -/
lemma exists_quadratic_crossing (T x : ℝ) (hT : 0 < T) :
    ∃ n : ℕ, x ≤ T * (n : ℝ) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (x / T))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnx : x / T < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hx : x < (n : ℝ) * T := (div_lt_iff₀ hT).mp hnx
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  exact ⟨n, hx.le.trans (by nlinarith [mul_le_mul_of_nonneg_left hsq hT.le])⟩
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped Topology
open PaperR9
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution
    (A B : ℕ → ℤ) (ξ α τ : ℝ) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hA : QuadExpUpper (fun n => (A n : ℝ)) α)
    (hL : QuadLogRate (fun n => (A n : ℝ) * ξ - B n) (-τ)) :
    ApproximationExponentUpper ξ (1 + α / τ) := by
  intro ν hν
  have hν1 : 1 < ν := by
    have : 0 ≤ α / τ := div_nonneg hα hτ.le
    linarith
  have hν0 : 0 < ν := by linarith
  let g : ℝ := ν * τ - (α + τ)
  have hg : 0 < g := by
    have hdiv : α / τ < ν - 1 := by linarith
    have := (div_lt_iff₀ hτ).mp hdiv
    dsimp [g]
    nlinarith
  let η : ℝ := min (τ / 2) (g / (2 * (ν + 2)))
  have hη : 0 < η := lt_min (half_pos hτ) (div_pos hg (by linarith))
  have hητ : η ≤ τ / 2 := min_le_left _ _
  have hηg : η * (2 * (ν + 2)) ≤ g := by
    exact (le_div_iff₀ (by linarith : 0 < 2 * (ν + 2))).mp (min_le_right _ _)
  let T : ℝ := τ - η
  let S : ℝ := α + τ + 2 * η
  let D : ℝ := ν * T - S
  let C : ℝ := ν * T + ν * |Real.log 2|
  have hT : 0 < T := by dsimp [T]; linarith
  have hS : 0 < S := by dsimp [S]; linarith
  have hD : 0 < D := by dsimp [D, T, S, g] at *; nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlow := hL.exp_lower hne η hη
  have hupp := hL.exp_upper η hη
  have hcoeff := hA η hη
  have hmesh := eventually_linear_le_square C D hC hD
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (((hlow.and hupp).and hcoeff).and hmesh)
  let N := max N₀ 1
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt (Real.exp (T * (N : ℝ) ^ 2))
  have hq₀pos : 0 < q₀ := by
    have : (0 : ℝ) < q₀ := (Real.exp_pos _).trans hq₀
    exact_mod_cast this
  refine ⟨q₀, hq₀pos, ?_⟩
  intro q hq p
  have hqpos : 0 < q := hq₀pos.trans_le hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqgt : Real.exp (T * (N : ℝ) ^ 2) < q :=
    hq₀.trans_le (by exact_mod_cast hq)
  have hlogq : T * (N : ℝ) ^ 2 < Real.log (q : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hqgt
    simpa using h
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogmul : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) hqR.ne'
  let ex := exists_quadratic_crossing T (Real.log (2 * (q : ℝ))) hT
  let n : ℕ := Nat.find ex
  have hcross : Real.log (2 * (q : ℝ)) ≤ T * (n : ℝ) ^ 2 := Nat.find_spec ex
  have hnN : N ≤ n := by
    by_contra hh
    have hnlt : n < N := Nat.lt_of_not_ge hh
    have hnle : (n : ℝ) ≤ N := by exact_mod_cast hnlt.le
    have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnle 2
    have hprod := mul_le_mul_of_nonneg_left hsq hT.le
    rw [hlogmul] at hcross
    linarith
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hnN
  have hn0 : 0 < n := by omega
  have hnN₀ : N₀ ≤ n := (le_max_left _ _).trans hnN
  obtain ⟨⟨⟨hlo, hup⟩, hAn⟩, hmn⟩ := hN₀ n hnN₀
  have hprev : T * ((n - 1 : ℕ) : ℝ) ^ 2 < Real.log (2 * (q : ℝ)) := by
    exact lt_of_not_ge (Nat.find_min ex (Nat.sub_lt hn0 (by decide)))
  have hprev' : T * ((n : ℝ) - 1) ^ 2 < Real.log 2 + Real.log (q : ℝ) := by
    simpa [Nat.cast_sub hn1, hlogmul] using hprev
  have hνT : 0 ≤ ν * T := mul_nonneg hν0.le hT.le
  have hνabs : 0 ≤ ν * |Real.log 2| := mul_nonneg hν0.le (abs_nonneg _)
  have hlinear : ν * T * (2 * (n : ℝ) - 1) + ν * Real.log 2 ≤
      C * (2 * (n : ℝ) + 1) := by
    have hfirst : ν * T * (2 * (n : ℝ) - 1) ≤
        ν * T * (2 * (n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hνT
    have hsecond : ν * Real.log 2 ≤ ν * |Real.log 2| * (2 * (n : ℝ) + 1) := by
      calc
        ν * Real.log 2 ≤ ν * |Real.log 2| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hν0.le
        _ = ν * |Real.log 2| * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          have hn0R : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith) hνabs
    dsimp [C]
    nlinarith
  have hmeshfinal : S * (n : ℝ) ^ 2 ≤ ν * Real.log (q : ℝ) := by
    have hprevν := mul_le_mul_of_nonneg_left hprev'.le hν0.le
    dsimp [sqScale, D] at hmn
    nlinarith
  have hsep : Real.exp (-(S * (n : ℝ) ^ 2)) ≤
      |ξ - (p : ℝ) / (q : ℝ)| := by
    have hh := separation_of_exponential_envelope (A n) (B n) p q ξ
      ((τ + η) * (n : ℝ) ^ 2) (T * (n : ℝ) ^ 2)
      ((α + η) * (n : ℝ) ^ 2) hqpos
      (by
        have he : (-τ - η) * sqScale n = -((τ + η) * (n : ℝ) ^ 2) := by
          unfold sqScale
          ring
        simpa only [he] using hlo)
      (by
        have he : (-τ + η) * sqScale n = -(T * (n : ℝ) ^ 2) := by
          dsimp [T, sqScale]
          ring
        simpa only [he] using hup)
      (by simpa [sqScale] using hAn) hcross
    have hid : (τ + η) * (n : ℝ) ^ 2 + (α + η) * (n : ℝ) ^ 2 =
        S * (n : ℝ) ^ 2 := by dsimp [S]; ring
    simpa only [hid] using hh
  calc
    (q : ℝ) ^ (-ν) = Real.exp (Real.log (q : ℝ) * (-ν)) :=
      Real.rpow_def_of_pos hqR _
    _ ≤ Real.exp (-(S * (n : ℝ) ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := hsep
