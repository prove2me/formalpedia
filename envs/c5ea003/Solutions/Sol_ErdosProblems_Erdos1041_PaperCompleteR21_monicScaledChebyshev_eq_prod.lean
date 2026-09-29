-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:58:31.641339+00:00
-- url     : https://prove2.me/submissions/f9040608-6d5b-46aa-9841-07d108a2dee2

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_chebNode_strictMono
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_eval_monicScaledChebyshev
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_monicScaledChebyshev_isMonicOfDegree
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

theorem isMonicOfDegree_prod_X_sub_C {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsMonicOfDegree (∏ i ∈ s, (X - C (a i))) s.card := by
  refine ⟨?_, monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)⟩
  rw [natDegree_prod _ _ fun i _ => (monic_X_sub_C (a i)).ne_zero]
  simp

/-! ### Sign alternation between consecutive root gaps -/



/-! ### Gap maxima -/



/-! ### The normalised core: a whole gap below `C_n` -/



/-! ### Transport between the root line and `ℝ` -/









/-! ### The sharp collinear root-diameter theorem -/



/-! ### The Erdős case: a short curve inside the unit lemniscate -/



/-! ### Sharpness: the scaled Chebyshev root configuration -/













private theorem endpointScale_pos' (m : ℕ) : 0 < endpointScale (m + 2) :=
  endpointScale_pos (Nat.le_add_left 2 m)











theorem eval_monicScaledChebyshev_chebNode (m : ℕ) (i : Fin (m + 2)) :
    (monicScaledChebyshev (m + 2)).eval (chebNode m i) = 0 := by
  have hn : 2 ≤ m + 2 := Nat.le_add_left 2 m
  have hr := endpointScale_pos' m
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eval_monicScaledChebyshev hn]
  have hx : endpointScale (m + 2) * chebNode m i
      = Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi
          / (2 * ((m + 2 : ℕ) : ℝ))) := by
    simp only [chebNode]
    field_simp
  rw [hx, Polynomial.Chebyshev.T_real_cos]
  have hzero : Real.cos ((((m + 2 : ℕ) : ℤ) : ℝ) *
      ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))) = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨((m + 1 - (i : ℕ) : ℕ) : ℤ), ?_⟩
    push_cast
    field_simp
  rw [hzero, mul_zero]
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i)) := by
  have hn : 2 ≤ m + 2 := Nat.le_add_left 2 m
  have h1 := monicScaledChebyshev_isMonicOfDegree (n := m + 2) hn
  have h2 : (∏ i : Fin (m + 2), (X - C (chebNode m i))).IsMonicOfDegree (m + 2) := by
    have h := isMonicOfDegree_prod_X_sub_C (R := ℝ)
      (Finset.univ : Finset (Fin (m + 2))) (chebNode m)
    simpa using h
  have hdeg : (monicScaledChebyshev (m + 2)
      - ∏ i : Fin (m + 2), (X - C (chebNode m i))).natDegree < m + 2 :=
    h1.natDegree_sub_lt (by simp) h2
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (monicScaledChebyshev (m + 2) - ∏ i : Fin (m + 2), (X - C (chebNode m i)))
    (f := chebNode m) (chebNode_strictMono m).injective
    (fun i => by
      rw [eval_sub, eval_monicScaledChebyshev_chebNode, eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp)]
      ring)
    (by simpa using hdeg)
  exact sub_eq_zero.mp hz
