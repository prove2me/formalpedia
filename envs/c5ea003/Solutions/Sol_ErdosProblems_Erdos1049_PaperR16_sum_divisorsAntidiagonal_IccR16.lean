-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.sum_divisorsAntidiagonal_IccR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:25:15.030521+00:00
-- url     : https://prove2.me/submissions/73ad652a-d38f-42b1-ac12-7f1104700d8d

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_antidiagonal_nonzeroR16
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# G02 arithmetic suppliers: the summatory totient with an explicit error

Proves |Σ_{d≤y} φ(d) - (3/π²)y²| ≤ 2y(1 + log(1+y)) for every real y ≥ 0.
The definitions below are genuine totient/Möbius sums. No asymptotic
supplier is assumed as an axiom, typeclass field, or theorem premise.
-/

namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000
end ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
theorem solution (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ r ∈ Icc 1 N, ∑ x ∈ r.divisorsAntidiagonal, F x.1 x.2) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N / a), F a b := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun z _ => (⟨z.2.1, z.2.2⟩ : Σ _ : ℕ, ℕ))
  · intro z hz
    obtain ⟨hr, hx⟩ := mem_sigma.mp hz
    have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
    obtain ⟨ha0, hb0⟩ := antidiagonal_nonzeroR16 hx
    have ha : 1 ≤ z.2.1 := by omega
    have hb : 1 ≤ z.2.2 := by omega
    have hrN := (mem_Icc.mp hr).2
    apply mem_sigma.mpr
    constructor
    · apply mem_Icc.mpr
      constructor
      · exact ha
      · have hmul : z.2.1 ≤ z.2.1 * z.2.2 := by nlinarith
        show z.2.1 ≤ N
        omega
    · apply mem_Icc.mpr
      refine ⟨hb, ?_⟩
      apply (Nat.le_div_iff_mul_le (by omega : 0 < z.2.1)).2
      nlinarith
  · rintro ⟨r, a, b⟩ hr ⟨s, c, d⟩ hs h
    have h' : a = c ∧ b = d := by simpa using h
    rcases h' with ⟨rfl, rfl⟩
    have hp := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hr).2).1
    have hq := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hs).2).1
    dsimp only at hp hq
    have hrs : r = s := by omega
    subst hrs
    rfl
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := mem_sigma.mp hab
    obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
    obtain ⟨hb1, hbN⟩ := mem_Icc.mp hb
    dsimp only at ha1 haN hb1 hbN
    have hp : a * b ≤ N := by
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < a)).1 hbN
      nlinarith
    refine ⟨⟨a * b, (a, b)⟩, ?_, rfl⟩
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨by nlinarith, hp⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩
  · intro z hz
    rfl
