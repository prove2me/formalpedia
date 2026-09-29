-- Prove2me | Definitions.Def_Bridges_NeuralCoding_LorentzianHardnessLowerBounds
-- name    : Bridges_NeuralCoding_LorentzianHardnessLowerBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:25.504934+00:00
-- url     : https://prove2.me/theorems/5ab98105-ac8a-407d-8fa0-e6d1de79401f
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_LorentzianHardnessLowerBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.LorentzianHardnessLowerBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/LorentzianHardnessLowerBounds.lean by skeleton subtraction
import Mathlib
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

namespace LorentzianHardness

/-! ## Core Definitions (compatible with catalog) -/

/-- The quadratic form induced by a matrix A: Q_A(x) = ∑ᵢ ∑ⱼ A(i,j) x(i) x(j). -/
def QuadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- A matrix has at most one positive eigenvalue (Lorentzian signature). -/
def HasAtMostOnePositiveEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ w : Fin n → ℝ, ∀ v : Fin n → ℝ,
    (∑ i, w i * v i = 0) → QuadForm A v ≤ 0

/-- The set of multiindices α : Fin n → ℕ with ∑ α = d. -/
def multiIndexSet (n d : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.univ (α := Fin n → Fin (d + 1))).image
    (fun f i => (f i : ℕ)) |>.filter (fun α => ∑ i, α i = d)

/-- The number of multiindices of weight d in n variables. -/
def multiIndexCount (n d : ℕ) : ℕ := (multiIndexSet n d).card

/-- The number of quadratic leaves in recursive recognition. -/
def numberOfQuadraticLeaves (n d : ℕ) : ℕ :=
  if d < 2 then 1 else multiIndexCount n (d - 2)

/-! ## Novel Definitions: CNF Formulas and Satisfaction -/

/-- A CNF formula over `n` Boolean variables, represented as a set of clauses,
    where each clause is a set of literals (variable index, polarity). -/
structure CNFFormula (n : ℕ) where
  clauses : Finset (Finset (Fin n × Bool))

/-- A literal is satisfied by an assignment if the variable value matches polarity. -/
def literalSatisfied {n : ℕ} (τ : Fin n → Bool) (ℓ : Fin n × Bool) : Prop :=
  τ ℓ.1 = ℓ.2

/-- A clause is satisfied if at least one literal is satisfied. -/
def clauseSatisfied {n : ℕ} (τ : Fin n → Bool) (C : Finset (Fin n × Bool)) : Prop :=
  ∃ ℓ ∈ C, literalSatisfied τ ℓ

/-- A CNF formula is satisfied if all clauses are satisfied. -/
def formulaSatisfied {n : ℕ} (τ : Fin n → Bool) (φ : CNFFormula n) : Prop :=
  ∀ C ∈ φ.clauses, clauseSatisfied τ C

/-- A CNF formula is satisfiable if there exists a satisfying assignment. -/
def CNFSatisfiable {n : ℕ} (φ : CNFFormula n) : Prop :=
  ∃ τ : Fin n → Bool, formulaSatisfied τ φ

/-! ## Novel Definition: Binary Multiindices and Assignment Encoding -/

/-- Convert a Boolean assignment to a binary multiindex (indicator function). -/
def assignmentToMultiIndex {n : ℕ} (τ : Fin n → Bool) : Fin n → ℕ :=
  fun i => if τ i then 1 else 0

/-- The set of binary (0/1-valued) multiindices of weight d in n variables,
    obtained from d-element subsets via indicator functions. -/
def binaryMultiIndexSet (n d : ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Fin n)).powersetCard d).image
    (fun S : Finset (Fin n) => fun i : Fin n => if i ∈ S then 1 else 0)

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

/-- A diagonal matrix: D(i,j) = d(i) if i = j, 0 otherwise. -/
def diagMatrix {n : ℕ} (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then d i else 0

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

/-! ## Conjecture: Branch-Complexity Barrier

**Conjecture (branch-complexity barrier)**:
There exists a constant c > 0 and an explicit family of homogeneous
polynomials p_d with nonnegative integer coefficients and degree d such
that every recursive Lorentzian certificate for p_d has size at least exp(c·d).

**Testable prediction**: For d = 2,3,...,7, exhaustive search over certificate
trees should reveal minimal certificate size growing superpolynomially in d.
A disproof would exhibit unexpectedly small certificates, suggesting a hidden
compression principle.

**Conjecture (SAT encoding exactness)**:
For the clause-encoding family P_φ, one has P_φ Lorentzian iff φ is unsatisfiable.
This is falsifiable by brute-force search on small CNF instances.
-/


/-! ## SAT-to-Branch Correspondence Structure

This section establishes the structural framework for encoding SAT
instances into derivative-tree branches. The key insight is that
Boolean assignments biject with binary multiindices, so the derivative
tree of a suitably constructed polynomial family mirrors the search
tree of a SAT solver.

**Strategy A sketch**: Given a CNF formula φ on n variables:
1. Map each assignment τ : Fin n → Bool to a binary multiindex via
   `assignmentToMultiIndex`.
2. The derivative branch at direction α corresponds to "selecting"
   variables according to α.
3. Branch obstruction (non-Lorentzian leaf) corresponds to unsatisfied
   clause patterns.
-/

/-- The weight (number of true variables) of a Boolean assignment. -/
def assignmentWeight {n : ℕ} (τ : Fin n → Bool) : ℕ :=
  Finset.card (Finset.univ.filter (fun i => τ i = true))

/-
Weight of assignmentToMultiIndex equals assignmentWeight.
-/

/-
The number of Boolean assignments of weight d to n variables is C(n, d).
-/

/-! ## Summary of the Complexity Landscape

The theorems in this file establish the following picture:

### Upper bounds (from catalog)
- `card_multiindex_le_pow`: multiIndexCount n d ≤ n^d
- `quadratic_leaf_count_le`: numberOfQuadraticLeaves n d ≤ n^(d-2)

### Lower bounds (this file)
- `multiindex_count_ge_choose`: multiIndexCount n d ≥ C(n, d)
- `central_choose_ge_two_pow`: C(2k, k) ≥ 2^k
- `leaf_count_exponential_in_degree`: numberOfQuadraticLeaves (2k) (k+2) ≥ 2^k

### Spectral bridge (this file)
- `diagonal_atMostOnePos_of_unique_pos`: ≤ 1 positive entry → Lorentzian
- `two_positive_diagonal_not_lorentzian`: 2 positive entries → not Lorentzian

### SAT bridge (this file)
- `binary_indicator_injective`: assignments inject into multiindices
- `assignment_multiindex_weight`: weight is preserved
- `count_assignments_of_weight`: C(n, d) assignments of each weight

Together, these results show that:
1. The derivative-tree leaf count is Θ(C(n, d)) up to polynomial factors.
2. When d ∼ n/2, this is exponential: 2^Ω(n).
3. Each leaf corresponds to a Boolean partial assignment.
4. The Lorentzian condition at each leaf is a spectral (eigenvalue) test.

This is the structural foundation for the full hardness theorem:
recognizing Lorentzianity in the unbounded-degree regime requires
exponentially many spectral tests, and these tests can encode SAT.
-/

end LorentzianHardness


