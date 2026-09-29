-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.sharpConstant_le_of_collinearDiameterBound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T04:08:43.995239+00:00
-- url     : https://prove2.me/submissions/787a9bb6-1e13-4e3e-a58b-2eeb142bbcdc

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_chebNode_strictMono
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_chebyshev_configuration_attains
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

/-- The tree's `comparisonBound` is the paper's `C_n`. -/
theorem comparisonBound_eq_inv {n : ℕ} (hn : 2 ≤ n) :
    comparisonBound n = (2 ^ (n - 1) * endpointScale n ^ n)⁻¹ := by
  have hr : 0 < endpointScale n := endpointScale_pos hn
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n :=
    mul_pos (by positivity) (pow_pos (inv_pos.mpr hr) n)
  show |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
      = (2 ^ (n - 1) * endpointScale n ^ n)⁻¹
  rw [abs_of_pos hpos, inv_pow, mul_inv]

/-- `comparisonBound n` written exactly as the paper's `C_n`. -/
theorem comparisonBound_eq {n : ℕ} (hn : 2 ≤ n) :
    comparisonBound n = 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) := by
  rw [comparisonBound_eq_inv hn, one_div]
  rfl





/-! ### A monic product of linear factors -/



/-! ### Sign alternation between consecutive root gaps -/



/-! ### Gap maxima -/



/-! ### The normalised core: a whole gap below `C_n` -/



/-! ### Transport between the root line and `ℝ` -/









/-! ### The sharp collinear root-diameter theorem -/



/-! ### The Erdős case: a short curve inside the unit lemniscate -/



/-! ### Sharpness: the scaled Chebyshev root configuration -/







































/-! ### "Best possible in every degree" -/
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [← comparisonBound_eq hn]
  obtain ⟨hgreat, hattain⟩ :=
    chebyshev_configuration_attains (m := m) (0 : ℂ) (1 : ℂ) (by simp) (R := 1) one_pos
      (∏ k : Fin (m + 2), (X - C ((0 : ℂ) + (1 : ℂ) * (((1 : ℝ) * chebNode m k : ℝ) : ℂ))))
      rfl
  obtain ⟨j, k, hjk, hyjk, hadj, _hlen, hseg⟩ :=
    hK (0 : ℂ) (1 : ℂ) (by simp) (fun k => (1 : ℝ) * chebNode m k) _ rfl (2 * 1) hgreat
  have hmono := chebNode_strictMono m
  have hjle : j ≤ k := hmono.le_iff_le.mp (by simpa using hyjk)
  have hjltk : j < k := lt_of_le_of_ne hjle hjk
  have hvlt : (j : ℕ) < (k : ℕ) := Fin.lt_def.mp hjltk
  have hklt := k.isLt
  have hadjval : (k : ℕ) = (j : ℕ) + 1 := by
    by_contra hcon
    have hgt : (j : ℕ) + 1 < (k : ℕ) := by omega
    have hlbound : (j : ℕ) + 1 < m + 2 := by omega
    rcases hadj ⟨(j : ℕ) + 1, hlbound⟩ with h | h
    · have hle := hmono.le_iff_le.mp (show chebNode m ⟨(j : ℕ) + 1, hlbound⟩ ≤ chebNode m j by
        simpa using h)
      rw [Fin.le_def] at hle
      simp only at hle
      omega
    · have hle := hmono.le_iff_le.mp (show chebNode m k ≤ chebNode m ⟨(j : ℕ) + 1, hlbound⟩ by
        simpa using h)
      rw [Fin.le_def] at hle
      simp only at hle
      omega
  have hjm : (j : ℕ) < m + 1 := by omega
  obtain ⟨z, hzmem, hzval⟩ := hattain ⟨(j : ℕ), hjm⟩
  have hij : (⟨(j : ℕ), hjm⟩ : Fin (m + 1)).castSucc = j := Fin.val_injective rfl
  have hik : (⟨(j : ℕ), hjm⟩ : Fin (m + 1)).succ = k :=
    Fin.val_injective (by simp only [Fin.val_succ]; omega)
  rw [hij, hik] at hzmem
  have hfinal := hseg z hzmem
  rw [hzval] at hfinal
  simpa using hfinal
