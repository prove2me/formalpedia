-- Prove2me | Theorems.Thm_LowDegreeTesting_low_degree_code_distance
-- name    : LowDegreeTesting.low_degree_code_distance
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:51:57.897037+00:00
-- url     : https://prove2.me/theorems/63ed0e6c-fd9f-41a1-8c44-65d05a7473eb
-- title:
--   Low degree code distance
-- statement:
--   Formal statement of `LowDegreeTesting.low_degree_code_distance` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LowDegreeTesting.low_degree_code_distance    {n d : ℕ} (S : Finset K)
--       (hS : d < S.card)
--       {p q : MvPolynomial (Fin n) K}
--       (hp : p.totalDegree ≤ d)
--       (hq : q.totalDegree ≤ d)
--       (hpq : ∃ x : Fin n → K, (∀ i, x i ∈ S) ∧
--         MvPolynomial.eval x p ≠ MvPolynomial.eval x q) :
--       S.card ^ n - d * S.card ^ (n - 1) ≤
--         ((Grid S n).filter
--           (fun x => MvPolynomial.eval x p ≠ MvPolynomial.eval x q)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/LowDegreeTesting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/LowDegreeTesting.lean#L357

-- Thm stub generated from Bridges/LowDegreeTesting.lean
import Mathlib
import Definitions.Def_Bridges_LowDegreeTesting
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

theorem LowDegreeTesting.low_degree_code_distance    {n d : ℕ} (S : Finset K)
    (hS : d < S.card)
    {p q : MvPolynomial (Fin n) K}
    (hp : p.totalDegree ≤ d)
    (hq : q.totalDegree ≤ d)
    (hpq : ∃ x : Fin n → K, (∀ i, x i ∈ S) ∧
      MvPolynomial.eval x p ≠ MvPolynomial.eval x q) :
    S.card ^ n - d * S.card ^ (n - 1) ≤
      ((Grid S n).filter
        (fun x => MvPolynomial.eval x p ≠ MvPolynomial.eval x q)).card := by sorry
