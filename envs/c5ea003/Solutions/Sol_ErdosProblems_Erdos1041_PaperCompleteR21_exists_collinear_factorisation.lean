-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:55:37.461461+00:00
-- url     : https://prove2.me/submissions/804fd53e-05e8-4c0a-bcf7-81154019184f

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



/-! ### The normalised core: a whole gap below `C_n` -/



/-! ### Transport between the root line and `ℝ` -/









/-! ### The sharp collinear root-diameter theorem -/



/-! ### The Erdős case: a short curve inside the unit lemniscate -/



/-! ### Sharpness: the scaled Chebyshev root configuration -/







































/-! ### "Best possible in every degree" -/







/-! ### From an abstract monic polynomial with collinear zeros -/
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ))) := by
  intro n
  induction n with
  | zero =>
      intro f hf _
      refine ⟨Fin.elim0, ?_⟩
      rw [isMonicOfDegree_zero_iff.mp hf]
      simp
  | succ n ih =>
      intro f hf hcol
      have hfne : f ≠ 0 := hf.ne_zero
      have hdeg : 0 < f.degree := by
        rw [Polynomial.degree_eq_natDegree hfne, hf.natDegree_eq]
        exact_mod_cast Nat.succ_pos n
      obtain ⟨z, hz⟩ := Complex.exists_root hdeg
      have hzmem : z ∈ f.roots := Polynomial.mem_roots'.mpr ⟨hfne, hz⟩
      obtain ⟨t, ht⟩ := hcol z hzmem
      obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hz
      have hfg : IsMonicOfDegree ((X - C z) * g) (1 + n) := by
        rw [Nat.add_comm 1 n, ← hg]
        exact hf
      have hgmono : g.IsMonicOfDegree n := (isMonicOfDegree_X_sub_one z).of_mul_left hfg
      have hgcol : ∀ w ∈ g.roots, ∃ s : ℝ, w = base + dir * (s : ℂ) := by
        intro w hw
        refine hcol w ?_
        rw [hg, Polynomial.roots_mul (by rw [← hg]; exact hfne)]
        exact Multiset.mem_add.mpr (Or.inr hw)
      obtain ⟨y, hy⟩ := ih g hgmono hgcol
      refine ⟨Fin.cons t y, ?_⟩
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← ht, ← hy]
      exact hg
