-- Prove2me | Definitions.Def_Bridges_NeuralCoding_LorentzianHardness
-- name    : Bridges_NeuralCoding_LorentzianHardness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:24.258737+00:00
-- url     : https://prove2.me/theorems/9cf07d62-b564-4428-859d-ff8ba53cc114
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_LorentzianHardness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.LorentzianHardness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/LorentzianHardness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Hardness of Unrestricted-Degree Lorentzian Recognition

This file establishes complexity lower bounds for recursive Lorentzian polynomial
recognition when the degree is unbounded, complementing the upper bounds in
`Catalog/Bridges/LorentzianRecognition.lean`.

## Main Results

* `central_binomial_lower_bound` — The central binomial coefficient C(2d, d) ≥ 2^d.
* `boolToMultiindex_injective` — An explicit injection from Boolean assignments to
  multiindices, the constructive core of the lower bound.
* `multiindex_count_exponential_lower` — The multiindex count grows exponentially:
  multiIndexCount (m+1) m ≥ 2^m.
* `leaf_count_exponential_lower_bound` — Quadratic leaf count in recursive
  Lorentzian recognition grows exponentially when degree is unbounded.
* `complexity_phase_transition` — Phase transition: polynomial for fixed degree,
  exponential for unbounded degree.
* `sat_obstruction_duality` — Cross-domain: unsatisfiability ↔ universal obstruction.
* `spectral_obstruction_non_lorentzian` — Cross-domain: spectral double-positivity
  implies non-Lorentzian signature.

## Strategy

We complement the catalog upper bound `quadratic_leaf_count_le` (≤ n^(d-2)) with
an exponential lower bound. The key construction is an injection from {0,1}^m into
multiindices of weight m in (m+1) variables.

## Application Keywords

coNP-hardness, Lorentzian polynomials, Hodge theory, algebraic combinatorics,
certificate complexity, SAT reduction, derivative trees, Hessian signatures,
spectral obstruction, parameterized complexity, proof complexity

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Cook, "The complexity of theorem-proving procedures", STOC 1971
-/

open Finset BigOperators

noncomputable section

namespace LorentzianHardness

/-! ## Catalog Definitions (from LorentzianRecognition.lean)

We restate the key definitions needed from the catalog file so this file
is self-contained and buildable independently.
-/

/-- The quadratic form Q_A(x) = ∑ᵢ ∑ⱼ A(i,j) x(i) x(j). -/
def QuadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- Lorentzian signature: at most one positive eigenvalue direction. -/
def HasAtMostOnePositiveEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ w : Fin n → ℝ, ∀ v : Fin n → ℝ,
    (∑ i, w i * v i = 0) → QuadForm A v ≤ 0


/-- The set of multiindices α : Fin n → ℕ with ∑ α = d. -/
def multiIndexSet (n d : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.univ (α := Fin n → Fin (d + 1))).image
    (fun f i => (f i : ℕ)) |>.filter (fun α => ∑ i, α i = d)

/-- The number of multiindices of weight d in n variables. -/
def multiIndexCount (n d : ℕ) : ℕ :=
  (multiIndexSet n d).card


/-- The number of quadratic leaves in recursive Lorentzian recognition. -/
def numberOfQuadraticLeaves (n d : ℕ) : ℕ :=
  if d < 2 then 1 else multiIndexCount n (d - 2)

/-
Upper bound: numberOfQuadraticLeaves n d ≤ n^(d-2) (from catalog).
-/

/-! ## Part 1: CNF Satisfiability Framework -/

/-- A CNF formula over n Boolean variables. -/
structure CNFFormula (n : ℕ) where
  clauses : List (List (Fin n × Bool))

/-- A literal is satisfied when the assignment matches its polarity. -/
def literalSatisfied {n : ℕ} (τ : Fin n → Bool) (lit : Fin n × Bool) : Prop :=
  τ lit.1 = lit.2

/-- A clause is satisfied if at least one literal is satisfied. -/
def clauseSatisfied {n : ℕ} (τ : Fin n → Bool) (C : List (Fin n × Bool)) : Prop :=
  ∃ lit ∈ C, literalSatisfied τ lit

/-- A formula is satisfied if all clauses are satisfied. -/
def formulaSatisfied {n : ℕ} (φ : CNFFormula n) (τ : Fin n → Bool) : Prop :=
  ∀ C ∈ φ.clauses, clauseSatisfied τ C

/-- A formula is satisfiable if some assignment satisfies it. -/
def CNFSatisfiable {n : ℕ} (φ : CNFFormula n) : Prop :=
  ∃ τ, formulaSatisfied φ τ

/-- A clause is an obstruction for an assignment if not satisfied. -/
def isClauseObstruction {n : ℕ} (τ : Fin n → Bool)
    (C : List (Fin n × Bool)) : Prop :=
  ¬ clauseSatisfied τ C

/-- An assignment is obstructed if some clause is unsatisfied. -/
def isObstructed {n : ℕ} (φ : CNFFormula n) (τ : Fin n → Bool) : Prop :=
  ∃ C ∈ φ.clauses, isClauseObstruction τ C

/-- The number of partial assignments for n variables. -/
def numPartialAssignments (n : ℕ) : ℕ := 2 ^ n

/-! ## Part 2: Central Binomial Coefficient Lower Bound -/

/-
**Central binomial lower bound**: C(2d, d) ≥ 2^d for all d.
    Proof by induction using C(2(d+1), d+1) = 2·C(2d+1, d) ≥ 2·C(2d, d).
-/

/-! ## Part 3: Boolean-to-Multiindex Injection -/

/-- Count true entries in a Boolean function on Fin m. -/
def countTrue (m : ℕ) (b : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

/-- The injection from Bool^m to multiindices of weight m in (m+1) variables.
    α_b(0) = m - countTrue(b), α_b(i+1) = b(i).toNat -/
def boolToMultiindex (m : ℕ) (b : Fin m → Bool) : Fin (m + 1) → ℕ :=
  fun i =>
    if h : i.val = 0 then m - countTrue m b
    else if h2 : i.val - 1 < m then (b ⟨i.val - 1, h2⟩).toNat
    else 0

/-
countTrue is at most m.
-/

/-
The multiindex from boolToMultiindex has weight m.
-/

/-
boolToMultiindex is injective.
-/

/-! ## Part 4: Exponential Lower Bound -/

/-
**Exponential multiindex lower bound**: multiIndexCount (m+1) m ≥ 2^m.
    The injection from {0,1}^m into multiindices proves this.
-/

/-
**Exponential leaf count lower bound**: When degree d = m+2, n = m+1,
    the number of quadratic leaves is at least 2^m.
-/

/-! ## Part 5: Complexity Phase Transition -/

/-
**Phase Transition**: For n = m+1, d = m+2:
    2^m ≤ numberOfQuadraticLeaves (m+1) (m+2) ≤ (m+1)^m
-/

/-! ## Part 6: Cross-Domain — SAT Obstruction Duality -/

/-
**Satisfiability-Obstruction Duality**: A formula is unsatisfiable iff
    every assignment is obstructed. This is the Boolean analogue of
    "every derivative branch has an obstruction."
-/

/-! ## Part 7: Cross-Domain — Spectral Obstruction -/


/-- A matrix has a second positive direction orthogonal to any given w. -/
def HasSecondPositiveDirection {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : Prop :=
  ∃ v : Fin n → ℝ, (∑ i, w i * v i = 0) ∧ QuadForm A v > 0

/-
**Spectral Obstruction**: If for every direction w there exists an
    orthogonal direction with positive quadratic form, then A does NOT
    have Lorentzian signature. This is the contrapositive of the
    Lorentzian definition and the key spectral obstruction lemma.
-/

/-! ## Part 8: Certificate Complexity -/

/-- Certificate complexity = number of quadratic leaves. -/
def lorentzianCertificateComplexity (n d : ℕ) : ℕ :=
  numberOfQuadraticLeaves n d

/-
Certificate complexity is exponential for unbounded degree.
-/

/-! ## Part 9: CNF Branch Correspondence -/

/-
**Cross-Domain Bridge**: Lorentzian recognition requires at least as many
    derivative branch inspections as SAT solving requires truth assignments.
-/

/-! ## Conjectures

**Conjecture (Branch-Complexity Barrier)**: There exists c > 0 and an explicit
family of homogeneous polynomials p_d with nonneg integer coefficients and
degree d such that every recursive Lorentzian certificate for p_d has size
at least exp(c·d).

Testable: For d = 2..7, minimal certificate sizes should grow superpolynomially.

**Conjecture (SAT Encoding Exactness)**: For a suitable clause-encoding
family P_φ, P_φ is Lorentzian iff φ is unsatisfiable.

Testable: Brute-force on small CNF (≤ 5 vars, ≤ 10 clauses) should verify.
-/

end LorentzianHardness


