-- Prove2me | Theorems.Thm_LowDegreeTesting_grid_schwartz_zippel_succ
-- name    : LowDegreeTesting.grid_schwartz_zippel_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:51:48.635599+00:00
-- url     : https://prove2.me/theorems/0061dee1-d11d-4ac6-b36b-6252c17904fa
-- title:
--   Grid schwartz zippel succ
-- statement:
--   Formal statement of `LowDegreeTesting.grid_schwartz_zippel_succ` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LowDegreeTesting.grid_schwartz_zippel_succ(n : ℕ) (S : Finset K)
--       (p : MvPolynomial (Fin (n + 1)) K)
--       (hp : p ≠ 0) (hS : p.totalDegree < S.card)
--       (ih : ∀ (q : MvPolynomial (Fin n) K), q ≠ 0 → q.totalDegree < S.card →
--         ((Grid S n).filter (fun x => MvPolynomial.eval x q = 0)).card
--         ≤ q.totalDegree * S.card ^ (n - 1)) :
--       ((Grid S (n + 1)).filter (fun x => MvPolynomial.eval x p = 0)).card
--       ≤ p.totalDegree * S.card ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/LowDegreeTesting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/LowDegreeTesting.lean#L201

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

theorem LowDegreeTesting.grid_schwartz_zippel_succ(n : ℕ) (S : Finset K)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ≠ 0) (hS : p.totalDegree < S.card)
    (ih : ∀ (q : MvPolynomial (Fin n) K), q ≠ 0 → q.totalDegree < S.card →
      ((Grid S n).filter (fun x => MvPolynomial.eval x q = 0)).card
      ≤ q.totalDegree * S.card ^ (n - 1)) :
    ((Grid S (n + 1)).filter (fun x => MvPolynomial.eval x p = 0)).card
    ≤ p.totalDegree * S.card ^ n := by sorry
