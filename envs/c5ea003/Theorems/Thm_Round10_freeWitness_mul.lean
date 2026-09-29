-- Prove2me | Theorems.Thm_Round10_freeWitness_mul
-- name    : Round10.freeWitness_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:24.219459+00:00
-- url     : https://prove2.me/theorems/066cb058-bceb-4afa-aaf4-1b4d913cd131
-- title:
--   Multiplicativity of the free-witness family.
-- statement:
--   **Multiplicativity of the free-witness family.**  Coprime moduli contribute
--   independently: the CRT-separability that the trace lemma formalises.
--
--   ```lean
--   theorem Round10.freeWitness_mul{m n : ℕ} (h : Nat.Coprime m n) (k : ℕ) :
--       freeWitness (m * n) k = freeWitness m k * freeWitness n k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/SquarefreeTrace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/SquarefreeTrace.lean#L26

-- Thm stub generated from Geometry/Round10Closures/SquarefreeTrace.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
/-
Round-10 Closures — Part VIII (cycle 3): the trace lemma beyond semiprimes.

Cycle 3 pushes the classification off the semiprime case: the free-witness family is
multiplicative, so for every squarefree modulus `N = ∏_{r ∈ P} r` (a finite set of distinct
primes) the witness is the product of the local gcd-residue coordinates,

    R_k(N) = ∏_{r ∈ P} gcd(k, r - 1).

Two consequences are recorded:

* the population of square roots of unity is `2^ω(N)` for odd squarefree `N`, so the
  residue coordinate *counts the prime factors* — the classified coordinate already knows
  `ω(N)`, while it still cannot name a single factor without aggregation;
* the witness of the exponent `k` is still bounded by `k^{ω(N)}`, so the bounded-exponent
  barrier of `JointClosure.lean` degrades only polynomially in the number of factors.
-/

open Round10

theorem Round10.freeWitness_mul{m n : ℕ} (h : Nat.Coprime m n) (k : ℕ) :
    freeWitness (m * n) k = freeWitness m k * freeWitness n k := by sorry
