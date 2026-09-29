-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_max
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:32.697209+00:00
-- url     : https://prove2.me/submissions/47955626-c076-4d49-b79e-bada564576c2

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Mathlib
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Erdős 1041: the sharp Chebyshev bound for collinear roots, with sharpness

Paper-form restatement of

* `res:sharp-collinear-root-diameter`
  (`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 1155),
* `thm:sharp-collinear-diameter`
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1715),
* `cor:collinear-erdos-1041`
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1769).

A monic complex polynomial of degree `n` whose zero occurrences are collinear is
written here in its factored form `∏ k, (X - C (base + dir * y k))` with
`‖dir‖ = 1` and `y : Fin n → ℝ`: that is exactly "monic of degree `n` with all
zero occurrences on one line", the line being `base + dir * ℝ`.  The diameter
`D` of the zero occurrences is carried as the hypothesis that `D` is the
greatest pairwise distance between zero occurrences.

The existing tree modules `SharpCollinearAlternation` and
`SharpCollinearChebyshev` supply the alternation/Chebyshev kernel: for a monic
real `p` of degree `m + 2` vanishing at `±1` and alternating in sign at `m + 1`
ordered interior points, one of those points has `|p| ≤ comparisonBound (m+2)`.
This file supplies everything the paper's proof needs around that kernel:

* the rigid normalisation (translation, rotation, scaling by `R = D/2`) and the
  transport identity `‖f (base + dir * s)‖ = R ^ n * |q ((s - mid)/R)|`;
* the existence of a maximiser of `|q|` in each root gap, and the fact that it
  is interior;
* the sign alternation of those gap maxima, proved directly from the product
  form of `q`;
* the upgrade from the kernel's pointwise conclusion to a bound on the WHOLE
  selected segment, which is where "`c i` is the gap maximum" is used;
* the repeated-zero (constant path) case;
* the sharpness clauses: the scaled Chebyshev configuration, its extreme zeros
  at distance `D`, a point of every adjacent gap at which the bound is attained
  with equality, and hence that no smaller constant works in any degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21
open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev

/-! ### The constant `C_n = 1 / (2^(n-1) cos^n (π/(2n)))` -/









/-! ### A monic product of linear factors -/



/-! ### Sign alternation between consecutive root gaps -/



/-! ### Gap maxima -/
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution {m : ℕ} (Y : Fin (m + 2) → ℝ) (hY : StrictMono Y)
    (i : Fin (m + 1)) :
    ∃ c, c ∈ Ioo (Y i.castSucc) (Y i.succ) ∧
      ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
        |∏ j, (x - Y j)| ≤ |∏ j, (c - Y j)| := by
  classical
  have hlt : Y i.castSucc < Y i.succ := hY i.castSucc_lt_succ
  have hcont : Continuous fun x : ℝ => |∏ j, (x - Y j)| := by
    apply Continuous.abs
    exact continuous_finset_prod _ fun j _ => continuous_id.sub continuous_const
  obtain ⟨c, hcmem, hcmax'⟩ :=
    (isCompact_Icc (a := Y i.castSucc) (b := Y i.succ)).exists_isMaxOn
      (Set.nonempty_Icc.mpr hlt.le) hcont.continuousOn
  have hcmax : ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ |∏ j, (c - Y j)| := isMaxOn_iff.mp hcmax'
  -- interior points are not roots
  have hne : ∀ x : ℝ, Y i.castSucc < x → x < Y i.succ → (∏ j, (x - Y j)) ≠ 0 := by
    intro x h1 h2
    refine Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_
    rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with h | h
    · have hjge : i.succ ≤ j := by
        rw [Fin.le_def, Fin.val_succ]; omega
      have := hY.monotone hjge
      intro hEq; rw [← hEq] at this; linarith
    · have hjle : j ≤ i.castSucc := by
        rw [Fin.le_def, Fin.val_castSucc]; omega
      have := hY.monotone hjle
      intro hEq; rw [← hEq] at this; linarith
  -- the endpoints are roots
  have hzero : ∀ a : Fin (m + 2), (∏ j, (Y a - Y j)) = 0 := fun a =>
    Finset.prod_eq_zero (Finset.mem_univ a) (by ring)
  set mid : ℝ := (Y i.castSucc + Y i.succ) / 2 with hmid
  have hmid1 : Y i.castSucc < mid := by rw [hmid]; linarith
  have hmid2 : mid < Y i.succ := by rw [hmid]; linarith
  have hmidpos : 0 < |∏ j, (mid - Y j)| := abs_pos.mpr (hne mid hmid1 hmid2)
  have hcpos : 0 < |∏ j, (c - Y j)| :=
    lt_of_lt_of_le hmidpos (hcmax mid ⟨hmid1.le, hmid2.le⟩)
  refine ⟨c, ⟨?_, ?_⟩, hcmax⟩
  · refine lt_of_le_of_ne hcmem.1 (fun hEq => ?_)
    rw [← hEq, hzero i.castSucc] at hcpos
    simp at hcpos
  · refine lt_of_le_of_ne hcmem.2 (fun hEq => ?_)
    rw [hEq, hzero i.succ] at hcpos
    simp at hcpos
