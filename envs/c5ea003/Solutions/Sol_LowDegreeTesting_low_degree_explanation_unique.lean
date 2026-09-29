-- Prove2me | solution 1 for LowDegreeTesting.low_degree_explanation_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:03:01.458383+00:00
-- url     : https://prove2.me/submissions/3714c088-be3e-4403-bf7d-27af87c37ebc

-- Sol generated from Bridges/LowDegreeTesting.lean
import Mathlib
import Definitions.Def_Bridges_LowDegreeTesting
import Theorems.Thm_LowDegreeTesting_mvpoly_eq_on_grid_of_agree_many
/-
# Low-Degree Testing over Finite Grids

This file formalizes the **finite-grid uniqueness and testability principle** for
multivariate polynomials: on a Cartesian product grid S^n ⊆ K^n, a nonzero polynomial
of bounded total degree cannot vanish on too many grid points.

This is the combinatorial soundness theorem underlying:
- **Reed–Muller codes**: evaluation codes with explicit minimum distance
- **Low-degree testing**: random agreement tests are sound
- **Self-correction**: uniqueness enables correction from noisy oracles
- **PCP/sum-check**: algebraic proof systems rely on polynomial rigidity

## Main results

- `grid_schwartz_zippel`: A nonzero polynomial of total degree d < |S| has at most
  d · |S|^(n-1) zeros on the grid S^n. This is the finite-grid Schwartz–Zippel bound.

- `mvpoly_eq_on_grid_of_agree_many`: If two bounded-degree polynomials agree on more
  than d · |S|^(n-1) grid points, they agree on all grid points.

- `low_degree_explanation_unique`: Two low-degree polynomials that each explain too much
  of the same data must agree on the entire grid.

- `low_degree_code_distance`: Distinct bounded-degree polynomials disagree on at least
  |S|^n - d · |S|^(n-1) grid points (Reed–Muller minimum distance).

## References

- Schwartz (1980), Zippel (1979): Probabilistic polynomial identity testing
- Reed–Muller codes: Evaluation codes over finite grids
- Arora–Barak: Computational Complexity, Chapter 19 (Low-degree testing)
-/


open Classical in
noncomputable section

open LowDegreeTesting

open MvPolynomial Polynomial Finset BigOperators

variable {K : Type*} [Field K] [DecidableEq K]

/-! ## Section 1: Grid Definition and Basic Properties -/


@[simp]
theorem mem_Grid {S : Finset K} {n : ℕ} {x : Fin n → K} :
    x ∈ Grid S n ↔ ∀ i, x i ∈ S :=
  Fintype.mem_piFinset

theorem Grid_card (S : Finset K) (n : ℕ) : (Grid S n).card = S.card ^ n := by
  simp [Grid, Fintype.card_piFinset]

/-! ## Section 2: Univariate Root Bound in a Finite Set -/

/-
A nonzero univariate polynomial of degree d has at most d roots in any finite set.
-/

/-! ## Section 3: Fiber Decomposition -/


/-
Evaluating the fiber polynomial at t gives eval (Fin.cons t a) p.
-/

/-
The fiber zero count decomposes as a sum over the smaller grid.
-/

/-! ## Section 4: Coefficient Degree Bound -/

/-
Total degree of the j-th coefficient of finSuccEquiv is at most totalDegree - j.
-/

/-
The leading coefficient (in the finSuccEquiv sense) is nonzero when f is nonzero.
-/

/-
The natDegree of the fiber polynomial is at most the natDegree of finSuccEquiv.
-/


/-! ## Section 5: Main Grid Zero Count Theorem -/

/-
Base case: a nonzero polynomial in 0 variables has no zeros on S^0.
-/

/-
When the leading coefficient evaluates to nonzero, the fiber polynomial is nonzero.
-/

/-
Bound on fiber zero count for good fibers (leading coeff evaluates to nonzero).
-/

/-
The leading coefficient's total degree is bounded.
-/

/-
The degreeOf 0 is at most the totalDegree.
-/

/-
**Grid Schwartz–Zippel Theorem (inductive step)**:
-/


/-! ## Section 6: Uniqueness and Distance Corollaries -/

/-
**Theorem A: Finite-grid uniqueness from large agreement.**
    If two polynomials of total degree ≤ d < |S| agree on more than d · |S|^(n-1)
    grid points, they agree on all grid points.
-/

/-
The original Theorem B as stated in the assignment (with each polynomial agreeing
   with f on > d · |S|^(n-1) points individually) is FALSE. Counterexample:
   K = ℚ, S = {0,1,2}, n = 1, d = 1, p(x) = x, q(x) = 2-x, f(0) = 2, f(1) = 1, f(2) = 2.
   Both p and q agree with f on 2 > 1 = d·|S|^0 points, yet p ≠ q on S.

   The correct version requires the SUM of agreements to exceed |S|^n + d · |S|^(n-1),
   which ensures the overlap (intersection of the two agreement sets) exceeds d · |S|^(n-1).

**Theorem B (corrected): Uniqueness of a low-degree explanation for a noisy function.**
    If two degree-≤ d polynomials p and q have combined agreement with f exceeding
    |S|^n + d · |S|^(n-1), then p and q agree on all grid points.
    This is the unique decoding radius condition for Reed–Muller codes.
-/

/-
**Theorem C: Distance lower bound for distinct low-degree polynomials.**
    Distinct polynomials of total degree ≤ d < |S| disagree on at least
    |S|^n - d · |S|^(n-1) grid points (Reed–Muller minimum distance).
-/



open LowDegreeTesting in
theorem solution    {n d : ℕ} (S : Finset K)
    (hS : d < S.card)
    (f : (Fin n → K) → K)
    {p q : MvPolynomial (Fin n) K}
    (hp : p.totalDegree ≤ d)
    (hq : q.totalDegree ≤ d)
    (h_combined_agree : S.card ^ n + d * S.card ^ (n - 1) <
      ((Grid S n).filter
        (fun x => MvPolynomial.eval x p = f x)).card +
      ((Grid S n).filter
        (fun x => MvPolynomial.eval x q = f x)).card) :
    ∀ x : Fin n → K, (∀ i, x i ∈ S) →
      MvPolynomial.eval x p = MvPolynomial.eval x q := by
  apply mvpoly_eq_on_grid_of_agree_many S hS hp hq;
  -- Let $A = \{x \in \text{Grid } S n \mid \text{eval } x p = f x\}$ and $B = \{x \in \text{Grid } S n \mid \text{eval } x q = f x\}$.
  set A := Finset.filter (fun x => MvPolynomial.eval x p = f x) (Grid S n)
  set B := Finset.filter (fun x => MvPolynomial.eval x q = f x) (Grid S n);
  -- By the principle of inclusion-exclusion, we have $|A \cap B| \geq |A| + |B| - |S|^n$.
  have h_inclusion_exclusion : (A ∩ B).card ≥ A.card + B.card - (Grid S n).card := by
    rw [ ← Finset.card_union_add_card_inter ];
    exact Nat.sub_le_of_le_add <| by linarith [ show # ( A ∪ B ) ≤ # ( Grid S n ) from Finset.card_le_card fun x hx => by aesop ] ;
  refine' lt_of_lt_of_le _ ( h_inclusion_exclusion.trans ( Finset.card_mono _ ) );
  · exact lt_tsub_iff_left.mpr ( by rw [ Grid_card ] ; linarith );
  · intro x hx; aesop;
