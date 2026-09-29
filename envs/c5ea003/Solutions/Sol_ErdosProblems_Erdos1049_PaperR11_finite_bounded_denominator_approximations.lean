-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.finite_bounded_denominator_approximations
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:12:56.860002+00:00
-- url     : https://prove2.me/submissions/bc5ff8f4-759a-4ba3-923e-0aaaa70618fa

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
import Lean.Elab.Tactic.Omega
import Mathlib
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

namespace PaperR10
end PaperR10

namespace PaperR9
end PaperR9

/-!
# The supremum definition of the irrationality exponent

Bounds the supremum exponent, real and extended, from quadratic linear forms.
Denominators are positive naturals and numerators are arbitrary integers.
Finiteness of the numerators at bounded denominators is proved, not assumed.
The extended-real definition also covers an unbounded exponent set.
-/

namespace ErdosProblems.Erdos1049.PaperR11
open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10









lemma approximation_numerator_bound {ξ ν : ℝ} {p : ℤ} {q : ℕ}
    (hq : 0 < q)
    (h : |ξ - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)) :
    |(p : ℝ)| < (q : ℝ) * (|ξ| + (q : ℝ) ^ (-ν)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : |(p : ℝ) / (q : ℝ)| < |ξ| + (q : ℝ) ^ (-ν) := by
    calc
      |(p : ℝ) / (q : ℝ)| = |ξ - (ξ - (p : ℝ) / (q : ℝ))| := by
        congr 1
        ring
      _ ≤ |ξ| + |ξ - (p : ℝ) / (q : ℝ)| := abs_sub _ _
      _ < |ξ| + (q : ℝ) ^ (-ν) := by linarith
  rw [abs_div, abs_of_pos hqR] at hp
  simpa [mul_comm] using (div_lt_iff₀ hqR).mp hp
end ErdosProblems.Erdos1049.PaperR11

open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution (ξ ν : ℝ) (Q : ℕ) :
    {r : ℤ × ℕ | r ∈ reducedApproximationPairs ξ ν ∧ r.2 < Q}.Finite := by
  classical
  let B : ℝ := ∑ q ∈ Finset.range Q,
    (q : ℝ) * (|ξ| + (q : ℝ) ^ (-ν))
  obtain ⟨N, hN⟩ := exists_nat_gt B
  let box : Finset (ℤ × ℕ) :=
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).product (Finset.range Q)
  refine box.finite_toSet.subset ?_
  rintro ⟨p, q⟩ ⟨⟨hq, _, happ⟩, hqQ⟩
  have hs : (q : ℝ) * (|ξ| + (q : ℝ) ^ (-ν)) ≤ B := by
    apply Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) * (|ξ| + (j : ℝ) ^ (-ν)))
    · intro j hj
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · exact Finset.mem_range.mpr hqQ
  have hpN : |(p : ℝ)| < (N : ℝ) :=
    ((approximation_numerator_bound hq happ).trans_le hs).trans hN
  have hpLo : -(N : ℤ) ≤ p := by
    have h : -(N : ℝ) ≤ (p : ℝ) := (abs_lt.mp hpN).1.le
    exact_mod_cast h
  have hpHi : p ≤ (N : ℤ) := by
    have h : (p : ℝ) ≤ (N : ℝ) := (abs_lt.mp hpN).2.le
    exact_mod_cast h
  change (p, q) ∈ box
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpLo, hpHi⟩, Finset.mem_range.mpr hqQ⟩
