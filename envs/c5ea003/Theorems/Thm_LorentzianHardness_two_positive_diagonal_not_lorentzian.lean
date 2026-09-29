-- Prove2me | Theorems.Thm_LorentzianHardness_two_positive_diagonal_not_lorentzian
-- name    : LorentzianHardness.two_positive_diagonal_not_lorentzian
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:51:50.886043+00:00
-- url     : https://prove2.me/theorems/0e651272-d71b-4bc7-ad92-baa0acef3695
-- title:
--   Two positive diagonal not lorentzian
-- statement:
--   Formal statement of `LorentzianHardness.two_positive_diagonal_not_lorentzian` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LorentzianHardness.two_positive_diagonal_not_lorentzian{n : ℕ} (d : Fin n → ℝ)
--       (i j : Fin n) (hij : i ≠ j) (hdi : d i > 0) (hdj : d j > 0) :
--       ¬ HasAtMostOnePositiveEigenvalue (diagMatrix d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/LorentzianHardnessLowerBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/LorentzianHardnessLowerBounds.lean#L313

-- Thm stub generated from Bridges/NeuralCoding/LorentzianHardnessLowerBounds.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_LorentzianHardnessLowerBounds
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Exponential Lower Bounds for Lorentzian Recognition Complexity

This file establishes that the recursive derivative-tree approach to Lorentzian
polynomial recognition has intrinsic exponential complexity when the degree is
unbounded, complementing the polynomial upper bounds `card_multiindex_le_pow`
and `quadratic_leaf_count_le` from the catalog.

## Mathematical Context

Brändén and Huh (Annals of Mathematics, 2020) showed that a homogeneous polynomial
with nonneg coefficients is Lorentzian iff all degree-2 iterated partial derivatives
have Hessian with at most one positive eigenvalue. The catalog established that the
number of such quadratic leaves is at most n^(d-2) for a degree-d polynomial in n
variables. Here we prove the complementary **lower bound**: explicit polynomial
families force the leaf count to grow exponentially when degree scales with the
number of variables.

## Key Results

* `central_choose_ge_two_pow` — C(2k, k) ≥ 2^k, the central binomial coefficient
  lower bound driving the exponential explosion.
* `binary_indicator_injective` — Boolean assignments inject into multiindices,
  establishing the SAT-to-derivative-tree bridge.
* `card_binary_multiindex_eq_choose` — Binary multiindex count equals C(n, d).
* `multiindex_count_ge_choose` — multiIndexCount n d ≥ C(n, d) for d ≤ n.
* `leaf_count_exponential_in_degree` — Quadratic leaf count ≥ 2^k when degree
  and variable count scale together.
* `diagonal_atMostOnePos_of_unique_pos` — Diagonal matrices with at most one
  positive entry have Lorentzian signature (spectral cross-domain bridge).
* `two_positive_diagonal_not_lorentzian` — Diagonal matrices with two positive
  entries do NOT have Lorentzian signature.

## Cross-Domain Connections

- **Computational complexity ↔ Hodge positivity**: The exponential lower bound
  shows that derivative-tree certification has complexity barrier when degree
  is unbounded, connecting Lorentzian recognition to coNP-type hardness.
- **SAT ↔ derivative trees**: Boolean assignments biject with binary multiindices,
  so derivative branches encode partial truth assignments.
- **Spectral theory ↔ Lorentzian signature**: Diagonal matrix characterization
  bridges linear algebra to the recursive recognition predicate.

## Application Keywords

coNP-hardness, Lorentzian polynomials, Hodge theory, algebraic combinatorics,
certificate complexity, SAT reduction, derivative trees, Hessian signatures,
spectral obstruction, parameterized complexity, proof complexity, strong log-concavity

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
-/

open Finset BigOperators Matrix

noncomputable section

open LorentzianHardness

/-! ## Core Definitions (compatible with catalog) -/






/-! ## Novel Definitions: CNF Formulas and Satisfaction -/






/-! ## Novel Definition: Binary Multiindices and Assignment Encoding -/



/-! ## Novel Definition: Derivative Branch Count -/



/-! ## Membership Lemma -/


/-! ## Theorem 1: Binary Indicator Injectivity

Boolean assignments inject into multiindices. This is the fundamental
bridge between SAT (Boolean satisfiability) and derivative-tree structure:
distinct truth assignments correspond to distinct derivative directions.
-/

/-
The indicator function of a finset is injective: distinct subsets give
    distinct indicator functions.
-/

/-! ## Theorem 2: Binary Multiindex Count Equals Binomial Coefficient

The number of binary (0/1-valued) multiindices of weight d in n variables
equals the binomial coefficient C(n, d). This connects the derivative-tree
leaf structure to classical combinatorics.
-/

/-
Elements of binaryMultiIndexSet are in multiIndexSet.
-/

/-
The cardinality of the binary multiindex set equals C(n, d).
-/

/-! ## Theorem 3: Multiindex Count Lower Bound via Binary Multiindices

The total multiindex count is at least the binomial coefficient C(n, d).
This is the key lower bound complementing the catalog's upper bound
`card_multiindex_le_pow`: while the upper bound is n^d, the lower bound
is C(n, d), which is exponential when d ∼ n/2.
-/

/-
**Lower bound**: The number of multiindices of weight d in n variables
    is at least C(n, d).
-/

/-! ## Theorem 4: Central Binomial Coefficient Exponential Lower Bound

The central binomial coefficient C(2k, k) ≥ 2^k. This is the engine
driving the exponential explosion in derivative-tree complexity.

**Proof sketch**: By induction on k.
- Base: C(0, 0) = 1 ≥ 1 = 2^0.
- Step: C(2(k+1), k+1) = C(2k+1, k) + C(2k+1, k+1) by Pascal's rule.
  By Pascal, C(2k+1, k) ≥ C(2k, k) and C(2k+1, k+1) ≥ C(2k, k).
  So C(2k+2, k+1) ≥ 2 · C(2k, k) ≥ 2 · 2^k = 2^(k+1).
-/

/-
**Central binomial coefficient lower bound**: C(2k, k) ≥ 2^k.
    This is the combinatorial core of the complexity barrier.
-/

/-! ## Theorem 5: Exponential Leaf Count for Unbounded Degree

When the degree scales with the number of variables, the quadratic leaf
count grows exponentially. Specifically, for 2k variables and degree k+2,
there are at least 2^k quadratic leaves. This proves that the n^(d-2)
upper bound from `quadratic_leaf_count_le` is not merely an artifact of
naive counting: the derivative tree genuinely has exponential size in
the unbounded-degree regime.

**Strategy B realization**: This is the certificate-complexity lower bound
via explicit counting. It shows that ANY recursive Lorentzian certificate
must perform exponentially many Hessian checks when degree ∼ n/2.
-/

/-
**Leaf explosion theorem**: The number of quadratic leaves in recursive
    Lorentzian recognition is at least 2^k when n = 2k and d = k + 2.
    This establishes an exponential lower bound complementing the
    polynomial upper bound `quadratic_leaf_count_le`.
-/

/-! ## Cross-Domain Bridge: Spectral Obstruction

The following theorems connect Lorentzian signature (a Hodge-theoretic
condition) to spectral linear algebra. We characterize exactly when a
diagonal matrix has Lorentzian signature, establishing that the Lorentzian
condition precisely detects the number of positive eigenvalues.

**Strategy C realization**: This bridges spectral obstruction to Lorentzian
recognition, showing that eigenvalue positivity is directly encoded in
the derivative-tree leaf condition.
-/


/-
QuadForm of a diagonal matrix simplifies to a weighted sum of squares.
-/

/-! ## Theorem 6: Diagonal Matrix Lorentzian Characterization

If a diagonal matrix has at most one positive diagonal entry, it has
Lorentzian signature. This is the "spectral → Lorentzian" direction
of the cross-domain bridge.
-/

/-
**Spectral bridge (forward)**: A diagonal matrix with at most one positive
    entry has Lorentzian signature (at most one positive eigenvalue).
-/

/-! ## Theorem 7: Spectral Obstruction — Two Positive Entries Break Lorentzian

If a diagonal matrix has two distinct positive diagonal entries, it does
NOT have Lorentzian signature. This is the "obstruction" direction: having
two positive eigenvalues is an obstruction to Lorentzianity.

Combined with Theorem 6, this gives an exact characterization:
a diagonal matrix has Lorentzian signature iff at most one entry is positive.
-/

/-
**Spectral obstruction**: A diagonal matrix with two positive entries
    does NOT have Lorentzian signature.
-/

theorem LorentzianHardness.two_positive_diagonal_not_lorentzian{n : ℕ} (d : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (hdi : d i > 0) (hdj : d j > 0) :
    ¬ HasAtMostOnePositiveEigenvalue (diagMatrix d) := by sorry
