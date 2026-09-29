-- Prove2me | Definitions.Def_Applications_MaxDeterminant4x4
-- name    : Applications_MaxDeterminant4x4
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:32.646128+00:00
-- url     : https://prove2.me/theorems/3d1edb24-9700-47dd-838f-4de2c351bb29
-- title:
--   Aether Catalog definitions — Applications_MaxDeterminant4x4
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.MaxDeterminant4x4`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/MaxDeterminant4x4.lean by skeleton subtraction
import Mathlib
/-
# Extremal Determinants of `4 × 4` Integer Matrices with Bounded Entries

For a bound `B ≥ 0`, consider the integer matrices whose entries all lie in the
symmetric range `{-B, …, B}`.  How large can the determinant be?

This file studies the order‑`4` case, which is the smallest order for which a
*Hadamard matrix* exists and hence the first genuinely interesting instance of
the classical **maximal determinant problem**.

The headline results are:

* `hadamardMat_det` — an explicit `±B` matrix (a scaled order‑`4` Hadamard
  matrix) attains determinant `16 · B⁴`.  Its rows are mutually orthogonal
  (`hadamardMat_mul_transpose`), which is exactly the algebraic reason the
  determinant is as large as it can be.
* `abs_det_four_le` — every `4 × 4` matrix with entries bounded by `B` has
  `|det| ≤ 24 · B⁴` (the Leibniz/permutation bound, a specialisation of the
  general order‑`n` estimate `abs_det_le_factorial`).
* `maxDet_lower`, `maxDet_upper` — combining the two, the maximum determinant
  `M(B)` over this family satisfies `16 · B⁴ ≤ M(B) ≤ 24 · B⁴`, and the lower
  end is achieved.
* `claimed_lt_true` — the quantity `(2k-1)⁴ - 2(2k-1)² + 1`, once floated as a
  candidate for the maximum on the range `{-(2k-1), …, 2k-1}`, is not even an
  upper bound: for every `k ≥ 1` the explicit construction already exceeds it
  (and for `k = 1` the candidate is `0`, while the true value is `16`).

The exact value of `M(B)` is `16 · B⁴`; pinning the upper bound down from `24`
to `16` is precisely Hadamard's inequality (equivalently the Hadamard–Fischer
determinant inequality for positive‑semidefinite matrices), recorded as a future
direction.

-- !-- Lab Notes -- !--
-- Hypothesis: On the symmetric entry range of radius `B`, the largest `4 × 4`
--   determinant is `16 · B⁴`, achieved by a scaled Hadamard matrix, and the
--   originally circulated formula `(2k-1)⁴ - 2(2k-1)² + 1` is incorrect.
-- Experiment: Built the explicit `±B` Hadamard matrix and computed its
--   determinant (`16 B⁴`) and Gram matrix (`4B² · I`, i.e. orthogonal rows).
--   Bounded a generic determinant by the permutation sum (`24 B⁴`).  Evaluated
--   the circulated formula at `k = 1`: it gives `0`, whereas the construction
--   gives `16`.
-- Analysis: The construction is a true lower bound and the permutation sum a
--   true upper bound, bracketing the maximum in `[16 B⁴, 24 B⁴]`.  Orthogonality
--   of the rows is the structural certificate for the lower bound: it forces
--   `(det)² = det(A Aᵀ) = (4B²)⁴`.  The circulated formula is false — it
--   under‑counts by an order of magnitude and is negative-to-zero for small `k`.
-- Critique: The bracket is honest but not tight; the gap `24 → 16` is exactly
--   Hadamard's inequality, which is a nontrivial analytic input.  No theorem
--   here is vacuous: each has explicit numerical witnesses and the refutation is
--   a strict inequality with a concrete matrix.
-- Synthesis: A clean, self-contained account of the order-`4` maximal
--   determinant problem: exact achievability, a permutation upper bound, the
--   orthogonality certificate, and a rigorous refutation of the circulated
--   formula.
-- !-- End Lab Notes -- !--
-/

set_option maxHeartbeats 800000

open Matrix
open scoped Nat

namespace MaxDeterminant4x4


/-! ## The extremal construction: a scaled order-`4` Hadamard matrix -/

/-- A scaled order-`4` Hadamard matrix: all entries are `±B` and the rows are
mutually orthogonal. -/
def hadamardMat (B : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![B, B, B, B; B, -B, B, -B; B, B, -B, -B; B, -B, -B, B]





/-! ## Upper bounds via the permutation expansion -/




/-! ## The maximum, bracketed -/





/-! ## Refuting the circulated formula -/




end MaxDeterminant4x4


