-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T04:01:30.585995+00:00
-- url     : https://prove2.me/submissions/dd05db7d-6006-4a2d-8fbc-fed0408eceea

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_exists_gap_max
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_prod_pair_neg
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_exists_peak_le_comparisonBound
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
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2) := by
  classical
  have hcast0 : ((0 : Fin (m + 1)).castSucc) = (0 : Fin (m + 2)) :=
    Fin.val_injective (by simp)
  have hsucclast : ((Fin.last m).succ) = Fin.last (m + 1) :=
    Fin.val_injective (by simp)
  set q : ℝ[X] := ∏ j, (X - C (Y j)) with hqdef
  have hqeval : ∀ x : ℝ, q.eval x = ∏ j, (x - Y j) := by
    intro x; rw [hqdef]; simp [eval_prod]
  have hqmonic : q.IsMonicOfDegree (m + 2) := by
    have h := isMonicOfDegree_prod_X_sub_C (R := ℝ) (Finset.univ : Finset (Fin (m + 2))) Y
    rw [hqdef]
    simpa using h
  choose c hcIoo hcmax using fun i : Fin (m + 1) => exists_gap_max Y hY i
  -- basic order facts about the chosen points
  have hlo : ∀ i : Fin (m + 1), Y i.castSucc < c i := fun i => (hcIoo i).1
  have hhi : ∀ i : Fin (m + 1), c i < Y i.succ := fun i => (hcIoo i).2
  have hcSM : StrictMono c := by
    intro i i' h
    have hvi : (i : ℕ) < (i' : ℕ) := Fin.lt_def.mp h
    have h1 : i.succ ≤ i'.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
    exact lt_of_lt_of_le (hhi i) (le_trans (hY.monotone h1) (hlo i').le)
  have ha : (-1 : ℝ) < c 0 := by
    have := hlo 0
    rwa [hcast0, hY0] at this
  have hb : c (Fin.last m) < 1 := by
    have := hhi (Fin.last m)
    rwa [hsucclast, hY1] at this
  have hmemlow : ∀ i : Fin (m + 1), Y 0 ≤ Y i.castSucc := fun i =>
    hY.monotone (by rw [Fin.le_def]; simp)
  have hmemhigh : ∀ i : Fin (m + 1), Y i.succ ≤ Y (Fin.last (m + 1)) := fun i =>
    hY.monotone (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_last]; omega)
  have hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1 := by
    intro i
    rw [abs_le]
    constructor
    · have h1 := hmemlow i
      have h2 := hlo i
      rw [hY0] at h1; linarith
    · have h1 := hmemhigh i
      have h2 := hhi i
      rw [hY1] at h1; linarith
  have hpa : q.eval (-1) = 0 := by
    rw [hqeval, ← hY0]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 2))) (by ring)
  have hpb : q.eval 1 = 0 := by
    rw [hqeval, ← hY1]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last (m + 1))) (by ring)
  have hpalt : ∀ i : Fin m, q.eval (c i.castSucc) * q.eval (c i.succ) < 0 := by
    intro i
    rw [hqeval, hqeval]
    refine prod_pair_neg Y ((i.castSucc : Fin (m + 1)).succ) ?_ ?_ ?_ ?_
    · exact hhi i.castSucc
    · have h := hlo i.succ
      have heq : ((i.succ : Fin (m + 1)).castSucc) = ((i.castSucc : Fin (m + 1)).succ) :=
        Fin.val_injective (by simp)
      rwa [heq] at h
    · intro j hj
      have hjv := Fin.lt_def.mp hj
      simp only [Fin.val_succ, Fin.val_castSucc] at hjv
      have hjle : j ≤ (i.castSucc : Fin (m + 1)).castSucc := by
        rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc]; omega
      exact lt_of_le_of_lt (hY.monotone hjle) (hlo i.castSucc)
    · intro j hj
      have hjv := Fin.lt_def.mp hj
      simp only [Fin.val_succ, Fin.val_castSucc] at hjv
      have hjge : (i.succ : Fin (m + 1)).succ ≤ j := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_succ]; omega
      exact lt_of_lt_of_le (hhi i.succ) (hY.monotone hjge)
  obtain ⟨i, hi⟩ :=
    exists_peak_le_comparisonBound hqmonic hcSM ha hb hpa hpb hpalt hc_mem
  refine ⟨i, fun x hx => ?_⟩
  calc |∏ j, (x - Y j)| ≤ |∏ j, (c i - Y j)| := hcmax i x hx
    _ = |q.eval (c i)| := by rw [hqeval]
    _ ≤ comparisonBound (m + 2) := hi
