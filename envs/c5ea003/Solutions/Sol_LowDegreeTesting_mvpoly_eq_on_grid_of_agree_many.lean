-- Prove2me | solution 1 for LowDegreeTesting.mvpoly_eq_on_grid_of_agree_many
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:00:47.048848+00:00
-- url     : https://prove2.me/submissions/b0166da3-c76e-45cc-bda6-b388744a9eb5

-- Sol generated from Bridges/LowDegreeTesting.lean
import Mathlib
import Definitions.Def_Bridges_LowDegreeTesting
import Theorems.Thm_LowDegreeTesting_grid_schwartz_zippel_succ
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
theorem grid_schwartz_zippel_zero (S : Finset K) (p : MvPolynomial (Fin 0) K)
    (hp : p ≠ 0) :
    ((Grid S 0).filter (fun x => MvPolynomial.eval x p = 0)).card = 0 := by
  rw [ MvPolynomial.eq_C_of_isEmpty p ] at hp ⊢ ; aesop

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

/-- **Grid Schwartz–Zippel Theorem**: A nonzero polynomial of total degree d < |S|
    has at most d · |S|^(n-1) zeros on the grid S^n.

    This is the finite-grid analogue of the classical Schwartz–Zippel lemma,
    and forms the algebraic foundation of Reed–Muller codes, low-degree testing,
    and PCP soundness. -/
theorem grid_schwartz_zippel (n : ℕ) (S : Finset K) (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (hS : p.totalDegree < S.card) :
    ((Grid S n).filter (fun x => MvPolynomial.eval x p = 0)).card
    ≤ p.totalDegree * S.card ^ (n - 1) := by
  induction n with
  | zero => simp [grid_schwartz_zippel_zero S p hp]
  | succ n ih => exact grid_schwartz_zippel_succ n S p hp hS ih

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
    {p q : MvPolynomial (Fin n) K}
    (hp : p.totalDegree ≤ d)
    (hq : q.totalDegree ≤ d)
    (hag : d * S.card ^ (n - 1) <
      ((Grid S n).filter
        (fun x => MvPolynomial.eval x p = MvPolynomial.eval x q)).card) :
    ∀ x : Fin n → K, (∀ i, x i ∈ S) →
      MvPolynomial.eval x p = MvPolynomial.eval x q := by
  contrapose! hag;
  -- Let $r = p - q$. Then $r$ is a nonzero polynomial of total degree $\leq d$.
  set r : MvPolynomial (Fin n) K := p - q
  have hr_ne_zero : r ≠ 0 := by
    grind
  have hr_deg : r.totalDegree ≤ d := by
    exact le_trans ( MvPolynomial.totalDegree_sub _ _ ) ( max_le hp hq );
  -- By the Grid Schwartz-Zippel Theorem, the number of zeros of $r$ on $S^n$ is at most $d \cdot |S|^{n-1}$.
  have hr_zeros : ((Grid S n).filter (fun x => MvPolynomial.eval x r = 0)).card ≤ r.totalDegree * S.card ^ (n - 1) := by
    apply grid_schwartz_zippel n S r hr_ne_zero (by linarith);
  convert hr_zeros.trans ( Nat.mul_le_mul_right _ hr_deg ) using 1;
  simp +decide [ r, sub_eq_zero ]
