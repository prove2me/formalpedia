-- Prove2me | solution 1 for LowDegreeTesting.low_degree_code_distance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:00:46.492992+00:00
-- url     : https://prove2.me/submissions/491b00db-f9b3-45ed-9e35-dda79be2d193

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
    (hpq : ∃ x : Fin n → K, (∀ i, x i ∈ S) ∧
      MvPolynomial.eval x p ≠ MvPolynomial.eval x q) :
    S.card ^ n - d * S.card ^ (n - 1) ≤
      ((Grid S n).filter
        (fun x => MvPolynomial.eval x p ≠ MvPolynomial.eval x q)).card := by
  -- By hypothesis, there exists x in the grid where eval x p ≠ eval x q, hence eval x (p - q) ≠ 0, so p - q ≠ 0.
  have h_diff_ne_zero : p - q ≠ 0 := by
    exact sub_ne_zero_of_ne <| by rintro rfl; exact hpq.choose_spec.2 rfl;
  -- Apply the Schwartz-Zippel theorem to p - q.
  have h_schwarz_zippel : ((Grid S n).filter (fun x => (MvPolynomial.eval x) (p - q) = 0)).card ≤ (p - q).totalDegree * S.card ^ (n - 1) := by
    apply grid_schwartz_zippel n S (p - q) h_diff_ne_zero;
    exact lt_of_le_of_lt ( MvPolynomial.totalDegree_sub p q ) ( max_lt ( lt_of_le_of_lt hp hS ) ( lt_of_le_of_lt hq hS ) );
  -- The set of disagreeing points is the complement of the set of agreeing points in the grid.
  have h_complement : ((Grid S n).filter (fun x => (MvPolynomial.eval x) p ≠ (MvPolynomial.eval x) q)) = (Grid S n) \ ((Grid S n).filter (fun x => (MvPolynomial.eval x) (p - q) = 0)) := by
    grind;
  -- The total number of grid points is |S|^n.
  have h_total : (Grid S n).card = S.card ^ n := by
    exact?;
  rw [ h_complement, Finset.card_sdiff ];
  rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ];
  exact h_total.symm ▸ Nat.sub_le_sub_left ( h_schwarz_zippel.trans ( Nat.mul_le_mul_right _ ( MvPolynomial.totalDegree_sub _ _ |> le_trans <| max_le hp hq ) ) ) _
