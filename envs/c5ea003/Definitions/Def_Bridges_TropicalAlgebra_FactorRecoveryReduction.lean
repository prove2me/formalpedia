-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_FactorRecoveryReduction
-- name    : Bridges_TropicalAlgebra_FactorRecoveryReduction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:10.980866+00:00
-- url     : https://prove2.me/theorems/f6942d3f-044f-4a21-99c8-11d93687a0ab
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_FactorRecoveryReduction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.FactorRecoveryReduction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/FactorRecoveryReduction.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Factor Recovery as a Complete Hard Problem

This file formalizes a **many-one reduction** from tropical matrix factorization to
factor recovery, establishing that recovering a hidden pair `(A, B)` from a tropical
product matrix `M` is exactly the canonical search problem for tropical factorization.

## Main Results

* `tropMul` — Min-plus (tropical) matrix multiplication over `ℝ`.
* `IsTropicalFactorization` — Predicate for `M = A ⊗ B`.
* `Recoverable` — Existence of a factorization witness pair.
* `recover_pair_iff_factorization` — Recovery is equivalent to factorization.
* `tropMul_shift_invariant` — **Gauge symmetry**: shifting columns of `A` and rows of
  `B` by opposite vectors preserves the tropical product.
* `tropical_factorization_reduction` — Explicit many-one reduction via identity embedding.
* `RecoveryOracle` — Abstract oracle type for factor recovery.
* `oracle_recovery_yields_factorization_solver` — A correct recovery oracle yields
  a factorization solver.
* `factorization_nonunique` — Non-uniqueness of recovered keys under gauge symmetry.

## Cryptographic Significance

The gauge-invariance theorem shows that the recovery problem is factorization
**modulo tropical gauge symmetry**: the right hardness object is an equivalence class
of decompositions, not a unique secret key.
-/

open Matrix Finset

noncomputable section

variable {n m k : ℕ} [NeZero k]

/-! ## Core Definitions -/

/-- **Tropical (min-plus) matrix multiplication.**
`(A ⊗ B)(i,j) = min_t (A(i,t) + B(t,j))` over all intermediate indices `t : Fin k`. -/
def tropMul (A : Matrix (Fin n) (Fin k) ℝ) (B : Matrix (Fin k) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun i j => Finset.inf' Finset.univ Finset.univ_nonempty (fun t => A i t + B t j)

/-- A matrix `M` admits a tropical factorization through inner dimension `k`
when `tropMul A B = M`. -/
def IsTropicalFactorization
    (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin m) ℝ) : Prop :=
  tropMul A B = M

/-- The recovery problem: does there exist a witness pair `(A, B)` such that
`tropMul A B = M`? -/
def Recoverable (M : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin k) ℝ, ∃ B : Matrix (Fin k) (Fin m) ℝ,
    tropMul A B = M

/-! ## Gauge Symmetry: Shift Definitions -/

/-- Shift columns of `A` by a vector `c`: `A'(i,t) = A(i,t) + c(t)`. -/
def shiftA (A : Matrix (Fin n) (Fin k) ℝ) (c : Fin k → ℝ) :
    Matrix (Fin n) (Fin k) ℝ :=
  fun i t => A i t + c t

/-- Shift rows of `B` by the opposite vector: `B'(t,j) = B(t,j) - c(t)`. -/
def shiftB (B : Matrix (Fin k) (Fin m) ℝ) (c : Fin k → ℝ) :
    Matrix (Fin k) (Fin m) ℝ :=
  fun t j => B t j - c t

/-! ## Main Theorems -/


/-
**Gauge Symmetry Theorem.**
For any shift vector `c : Fin k → ℝ`, shifting columns of `A` by `+c` and rows
of `B` by `-c` preserves the tropical product. The terms
`(A i t + c t) + (B t j - c t)` simplify to `A i t + B t j` by cancellation.
-/


/-! ## Oracle Framework -/

/-- A **recovery oracle** optionally returns a factorization witness pair `(A, B)`. -/
def RecoveryOracle (n m k : ℕ) [NeZero k] :=
  Matrix (Fin n) (Fin m) ℝ →
    Option (Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin m) ℝ)

/-- A recovery oracle is **correct** if whenever it returns `some (A, B)`,
we have `tropMul A B = M`. -/
def OracleCorrect (oracle : RecoveryOracle n m k) : Prop :=
  ∀ M A B, oracle M = some (A, B) → tropMul A B = M

/-- A recovery oracle is **complete** if whenever `M` is recoverable,
the oracle returns `some`. -/
def OracleComplete (oracle : RecoveryOracle n m k) : Prop :=
  ∀ M, Recoverable (k := k) M → ∃ A B, oracle M = some (A, B)

/-
**Oracle Correctness Implies Factorization Solver.**
A correct and complete recovery oracle yields a factorization solver.
-/

/-
**Non-uniqueness of recovered keys.**
If `(A, B)` is a tropical factorization of `M`, then for any shift vector `c`,
the pair `(shiftA A c, shiftB B c)` is also a factorization of the same `M`.
-/

/-
**Bounded Recovery Hardness.**
Any recovery witness yields a full gauge-orbit of valid factorizations.
-/

end


