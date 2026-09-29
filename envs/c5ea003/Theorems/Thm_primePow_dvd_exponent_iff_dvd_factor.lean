-- Prove2me | Theorems.Thm_primePow_dvd_exponent_iff_dvd_factor
-- name    : primePow_dvd_exponent_iff_dvd_factor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:57.689293+00:00
-- url     : https://prove2.me/theorems/e0dafad0-6948-4f54-aac9-a1a25da0ddf7
-- title:
--   PrimePow dvd exponent iff dvd factor
-- statement:
--   Formal statement of `primePow_dvd_exponent_iff_dvd_factor` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem primePow_dvd_exponent_iff_dvd_factor    {n : ℕ} (hn : 0 < n) (S : InvariantFactorData n) (q : ℕ) (k : ℕ) (hq : Nat.Prime q) :
--       q ^ k ∣ S.exponent ↔ ∃ i : Fin n, q ^ k ∣ S.factors i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/ArithmeticStatistics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/ArithmeticStatistics.lean#L139

-- Thm stub generated from Bridges/PosetTheory/ArithmeticStatistics.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_ArithmeticStatistics
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Arithmetic Statistics of Graph Jacobians

This file establishes the deterministic algebraic backbone connecting
graph Jacobians (via Smith normal form invariant factors) to arithmetic
statistics in the spirit of Cohen–Lenstra heuristics.

## Mathematical Context

For a finite connected graph G, the **graph Jacobian** (also called the
critical group or sandpile group) is the finite abelian group
  Jac(G) ≅ ⊕ᵢ ℤ/dᵢℤ
where (d₁, …, dᵣ) are the Smith normal form invariant factors of a
reduced Laplacian of G. These invariant factors encode the complete
arithmetic structure of Jac(G).

The **Cohen–Lenstra heuristics** predict that for random graphs in suitable
regimes, the p-primary statistics of Jac(G) follow specific distributions.
This file proves the exact finite-n structural theorems that make such
predictions mathematically precise:

1. **Divisibility criterion** (Theorem A): q^k ∣ exp(Jac(G)) iff q^k divides
   some invariant factor.
2. **Prime-power moment identity** (Theorem B): The q^k-torsion count equals
   the product of gcd(dᵢ, q^k).
3. **Profile recovery** (Theorem C): The q-primary partition profile is
   recoverable from moment valuations via discrete differences.

## Main Definitions

* `InvariantFactorData` — Smith normal form data as a function from Fin n to ℕ
* `InvariantFactorData.exponent` — the exponent (lcm of all factors)
* `InvariantFactorData.primePowerMoment` — the q^k-torsion count
* `InvariantFactorData.qProfileCount` — the q-primary profile count
* `InvariantFactorProfile` — structure for q-primary partition data

## Cross-Domain Significance

These theorems bridge:
- **Graph theory ↔ Number theory**: Graph Jacobians are finite abelian groups
  whose arithmetic invariants obey the same algebraic laws as class groups.
- **Combinatorial probability ↔ Arithmetic statistics**: Random graph
  Laplacians produce groups whose laws match Cohen–Lenstra distributions.
- **Tropical geometry ↔ Arithmetic invariants**: The Jacobian is a
  tropical-harmonic object whose invariant factors obey number-theoretic
  statistics via the Smith normal form bridge.

## References

* Cohen, H. and Lenstra, H.W. "Heuristics on class groups" (1984)
* Clancy, J. et al. "Cohen–Lenstra for Jacobians of random graphs" (2015)
* Wood, M.M. "Sandpile groups of random graphs" (2017)
-/

open Finset BigOperators

/-! ## Core Structures -/


open InvariantFactorData

variable {n : ℕ}






/-! ## Invariant Factor Profile

A novel structure organizing the q-primary partition data of a finite abelian
group. This is the key statistical fingerprint for Cohen–Lenstra comparisons. -/


/-! ## Theorem A — Divisibility Criterion via Invariant Factors

For a finite abelian group ⊕ᵢ ℤ/dᵢℤ with exponent lcm(dᵢ), and a prime q:
  q^k ∣ lcm(dᵢ) ↔ ∃ i, q^k ∣ dᵢ

This is the fundamental arithmetic observable: the exponent is controlled
by the largest prime-power factor among all invariant factors.
-/

/-
**Theorem A (Divisibility Criterion)**: A prime power q^k divides the exponent
(lcm of invariant factors) if and only if it divides at least one invariant factor.

This is the exact arithmetic observable needed for comparing random graphs to
Cohen–Lenstra predictions: the exponent and largest invariant factor become
computable through SNF data.
-/

theorem primePow_dvd_exponent_iff_dvd_factor    {n : ℕ} (hn : 0 < n) (S : InvariantFactorData n) (q : ℕ) (k : ℕ) (hq : Nat.Prime q) :
    q ^ k ∣ S.exponent ↔ ∃ i : Fin n, q ^ k ∣ S.factors i := by sorry
