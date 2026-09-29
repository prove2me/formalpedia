-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_sharp_collinear_root_diameter_monic
-- name    : ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:46:23.42558+00:00
-- url     : https://prove2.me/theorems/d6293174-278a-4d7f-b89b-1f95cb82ba37
-- title:
--   Sharp diameter bound on one segment between collinear roots
-- statement:
--   Let $f\in\mathbb C[X]$ be monic of degree $n\ge2$. Suppose all its root occurrences lie on an affine line $b+d\mathbb R$, where $b,d\in\mathbb C$ and $|d|=1$. List those occurrences, with multiplicity, as $b+d y_i$ for real $y_i$. For any greatest pairwise distance $D$ among them, there are distinct indices $j,k$ with $y_j\le y_k$ and no listed coordinate strictly between them such that every $z$ on their closed segment satisfies $$|f(z)|\le\frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.$$ The selected indices can denote the same coordinate when roots repeat. The bound applies to one selected segment, not every pair; the separate equality and best-constant theorems establish sharpness. Will Cook authored the source paper and directed its research infrastructure (AI agents did most research and drafting; he did not independently verify every claim); Erdős–Herzog–Piranian had previously proved a contained collinear root segment under their stated hypotheses. Separately, [ani](https://www.erdosproblems.com/forum/thread/1041#post-8861) supplied the degree-seven Hausdorff counterexample to the broader #1041 benchmark; that counterexample is distinct from this sharp-collinear proof.
--
--   **Where to inspect the proof.** This page shows the theorem statement with a `by sorry` stub; the accepted proof is stored separately under **View graph → Solutions & Sketches**. That route may require sign-in. A [proved consequence](https://prove2.me/theorems/1b0f1b56-ceeb-4285-9add-d68b6a741272) imports this theorem in the same Lean environment.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L965-L981; paper theorem and historical comparison: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1193-L1246

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

open ErdosProblems.Erdos1041.PaperCompleteR21

theorem ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) :
    ∃ y : Fin n → ℝ, f = (∏ k, (X - C (base + dir * (y k : ℂ)))) ∧
      ∀ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖
              ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)
                * (D / 2) ^ n := by sorry
