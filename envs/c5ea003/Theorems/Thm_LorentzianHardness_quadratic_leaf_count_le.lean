-- Prove2me | Theorems.Thm_LorentzianHardness_quadratic_leaf_count_le
-- name    : LorentzianHardness.quadratic_leaf_count_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:51:01.264487+00:00
-- url     : https://prove2.me/theorems/1c1de3af-0d19-4f73-b6e3-503b203207a0
-- title:
--   Quadratic leaf count le
-- statement:
--   Formal statement of `LorentzianHardness.quadratic_leaf_count_le` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LorentzianHardness.quadratic_leaf_count_le(n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
--       numberOfQuadraticLeaves n d ≤ n ^ (d - 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/LorentzianHardness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/LorentzianHardness.lean#L101

-- Thm stub generated from Bridges/NeuralCoding/LorentzianHardness.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_LorentzianHardness
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

open LorentzianHardness

/-! ## Catalog Definitions (from LorentzianRecognition.lean)

We restate the key definitions needed from the catalog file so this file
is self-contained and buildable independently.
-/








/-
Upper bound: numberOfQuadraticLeaves n d ≤ n^(d-2) (from catalog).
-/

theorem LorentzianHardness.quadratic_leaf_count_le(n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
    numberOfQuadraticLeaves n d ≤ n ^ (d - 2) := by sorry
