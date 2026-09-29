-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.chebNode_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:28.150508+00:00
-- url     : https://prove2.me/submissions/bd53d76c-2a73-4e2c-9a0c-09b8c007d870

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
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



/-! ### The normalised core: a whole gap below `C_n` -/



/-! ### Transport between the root line and `ℝ` -/









/-! ### The sharp collinear root-diameter theorem -/



/-! ### The Erdős case: a short curve inside the unit lemniscate -/



/-! ### Sharpness: the scaled Chebyshev root configuration -/

private theorem angle_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.pi / b :=
  div_nonneg (mul_nonneg ha Real.pi_pos.le) hb.le

private theorem angle_le_pi {a b : ℝ} (hb : 0 < b) (h : a ≤ b) :
    a * Real.pi / b ≤ Real.pi := by
  have h1 : a / b ≤ 1 := (div_le_one hb).mpr h
  have h2 : a * Real.pi / b = Real.pi * (a / b) := by ring
  rw [h2]
  nlinarith [Real.pi_pos]

private theorem angle_lt {a a' b : ℝ} (hb : 0 < b) (h : a < a') :
    a * Real.pi / b < a' * Real.pi / b :=
  div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hb

/-- `cos` of an angle `a π / b` is strictly decreasing in `a` on the admissible
range `0 ≤ a' < a ≤ b`. -/
private theorem cos_angle_lt {a a' b : ℝ} (hb : 0 < b) (ha' : 0 ≤ a') (hab : a ≤ b)
    (h : a' < a) :
    Real.cos (a * Real.pi / b) < Real.cos (a' * Real.pi / b) :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg ha' hb) (angle_le_pi hb hab)
    (angle_lt hb h)





private theorem endpointScale_pos' (m : ℕ) : 0 < endpointScale (m + 2) :=
  endpointScale_pos (Nat.le_add_left 2 m)

private theorem twoN_pos (m : ℕ) : (0 : ℝ) < 2 * ((m + 2 : ℕ) : ℝ) := by
  have h : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (m + 1)
  linarith
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution (m : ℕ) : StrictMono (chebNode m) := by
  intro i i' h
  have hr := endpointScale_pos' m
  have hv : (i : ℕ) < (i' : ℕ) := Fin.lt_def.mp h
  have hilt := i.isLt
  have hi'lt := i'.isLt
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hbig : ((m + 1 - (i : ℕ) : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
    have h1 : (m + 1 - (i : ℕ) : ℕ) ≤ m + 1 := by omega
    have h2 : ((m + 1 - (i : ℕ) : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hsmall : ((m + 1 - (i' : ℕ) : ℕ) : ℝ) < ((m + 1 - (i : ℕ) : ℕ) : ℝ) := by
    have h1 : (m + 1 - (i' : ℕ) : ℕ) < (m + 1 - (i : ℕ) : ℕ) := by omega
    exact_mod_cast h1
  simp only [chebNode]
  apply div_lt_div_of_pos_right _ hr
  refine cos_angle_lt (twoN_pos m) (by positivity) ?_ (by linarith)
  rw [hcast]; linarith
