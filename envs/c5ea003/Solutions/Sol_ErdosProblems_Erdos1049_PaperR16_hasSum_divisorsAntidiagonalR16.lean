-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.hasSum_divisorsAntidiagonalR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:12:20.404355+00:00
-- url     : https://prove2.me/submissions/74a512c8-be12-411a-a9d4-6ce3c5e2f826

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
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
theorem solution (f g : ℕ → ℝ)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hf : Summable f) (hg : Summable g) :
    HasSum (fun n : ℕ => ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2)
      ((∑' a, f a) * (∑' b, g b)) := by
  have hprod : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) :=
    summable_mul_of_summable_norm hf.norm hg.norm
  have h := (hf.hasSum.mul hg.hasSum hprod).tsum_fiberwise
    (fun x : ℕ × ℕ => x.1 * x.2)
  convert h using 1
  funext n
  by_cases hn : n = 0
  · subst n
    have hz : ∀ x : ((fun x : ℕ × ℕ => x.1 * x.2) ⁻¹' {0} : Set (ℕ × ℕ)),
        f (x : ℕ × ℕ).1 * g (x : ℕ × ℕ).2 = 0 := by
      rintro ⟨⟨a, b⟩, hab⟩
      have hab' : a * b = 0 := hab
      rcases Nat.mul_eq_zero.mp hab' with ha | hb
      · simp [ha, hf0]
      · simp [hb, hg0]
    rw [Nat.divisorsAntidiagonal_zero, Finset.sum_empty, tsum_congr hz, tsum_zero]
  · rw [show (fun x : ℕ × ℕ => x.1 * x.2) ⁻¹' {n} =
        (n.divisorsAntidiagonal : Set (ℕ × ℕ)) by
          ext x
          simp [Nat.mem_divisorsAntidiagonal, hn],
      Finset.tsum_subtype' n.divisorsAntidiagonal (fun x => f x.1 * g x.2)]
