-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
-- name    : ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T03:43:13.911989+00:00
-- url     : https://prove2.me/theorems/b43dcf70-83b5-4881-9a4c-0dddc5482f8b
-- title:
--   Chebyshev nodes and the collinear diameter-bound predicate
-- statement:
--   For $m\ge0$, this bundle defines the indexed scaled Chebyshev root nodes and peak points for a degree-$(m+2)$ comparison polynomial. It also defines $\mathrm{CollinearDiameterBound}(n,K)$: every listed monic degree-$n$ polynomial with roots on a line and greatest pairwise root distance $D$ has some coordinate-adjacent root-occurrence segment on which $|f(z)|\le K(D/2)^n$ for every point $z$ of that segment. The two chosen indices must differ, but repeated roots may give the same coordinate. The bundle states this predicate; separate theorems establish which constants satisfy it.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L593-L604 and https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L858-L869

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
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









/-- The zeros of the endpoint-normalised scaled Chebyshev polynomial
`q_*(x) = T_n(r_n x) / (2^(n-1) r_n^n)` of degree `n = m + 2`, listed in
increasing order: `cos((2k+1)π/(2n)) / cos(π/(2n))`. -/
def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)

/-- The scaled Chebyshev extremum `cos(jπ/n) / cos(π/(2n))` lying inside the
`i`-th gap between consecutive nodes. -/
def chebPeak (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  Real.cos (((m + 1 - (i : ℕ) : ℕ) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ))
    / endpointScale (m + 2)



























/-! ### "Best possible in every degree" -/

/-- The conclusion of the sharp collinear diameter theorem, with the constant
left as a parameter `K`. -/
def CollinearDiameterBound (n : ℕ) (K : ℝ) : Prop :=
  ∀ base dir : ℂ, ‖dir‖ = 1 → ∀ (y : Fin n → ℝ) (f : ℂ[X]),
    f = (∏ k, (X - C (base + dir * (y k : ℂ)))) → ∀ D : ℝ,
      IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ K * (D / 2) ^ n





/-! ### From an abstract monic polynomial with collinear zeros -/








end ErdosProblems.Erdos1041.PaperCompleteR21


