-- Prove2me | Theorems.Thm_EulerTwoSquares_minmax_mem_repFinset
-- name    : EulerTwoSquares.minmax_mem_repFinset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:32:25.080819+00:00
-- url     : https://prove2.me/theorems/f09bf418-7944-4ad8-9ce9-3aa57b6d8ded
-- title:
--   A positive integral representation, normalised, is an element of `repFinset`.
-- statement:
--   A positive integral representation, normalised, is an element of `repFinset`.
--
--   ```lean
--   theorem EulerTwoSquares.minmax_mem_repFinset{n : ℕ} {U V : ℤ} (hU : 0 < U) (hV : 0 < V)
--       (h : U ^ 2 + V ^ 2 = (n : ℤ)) : ((min U V).toNat, (max U V).toNat) ∈ repFinset n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresRepCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresRepCount.lean#L34

-- Thm stub generated from Algebra/EulerTwoSquaresRepCount.lean
import Mathlib
import Definitions.Def_Algebra_EulerTwoSquaresRepCount

/-!
# The representation count, as a finite cardinality

`EulerTwoSquares.exactly_two_reps` describes the representations of `p*q` as a list of four
ordered integer pairs.  Here we package the same information as a *cardinality*: the finite
set of normalised representations

`repFinset n = {(a,b) : 0 < a ≤ b, a² + b² = n}`

has exactly two elements when `n = p*q` for distinct primes `p ≡ q ≡ 1 [MOD 4]`.  This is the
form in which the eligibility statistics of a factorisation experiment are actually measured.
-/

open EulerTwoSquares

variable {p q : ℕ}

theorem EulerTwoSquares.minmax_mem_repFinset{n : ℕ} {U V : ℤ} (hU : 0 < U) (hV : 0 < V)
    (h : U ^ 2 + V ^ 2 = (n : ℤ)) : ((min U V).toNat, (max U V).toNat) ∈ repFinset n := by sorry
