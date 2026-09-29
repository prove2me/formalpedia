-- Prove2me | Definitions.Def_Logic_NeuralCoding_BettiWhittakerPeriods
-- name    : Logic_NeuralCoding_BettiWhittakerPeriods
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:59:38.775753+00:00
-- url     : https://prove2.me/theorems/e9b6e7f3-78a9-4217-90c0-8d141a79e1b9
-- title:
--   Aether Catalog definitions — Logic_NeuralCoding_BettiWhittakerPeriods
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.NeuralCoding.BettiWhittakerPeriods`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/NeuralCoding/BettiWhittakerPeriods.lean by skeleton subtraction
import Mathlib
/-
  Betti–Whittaker Periods and Contragredient Representations of GL(n) — Core
  =========================================================================

  A regularity-free, fully algebraic model of the combinatorial heart of the
  Betti–Whittaker period relation for a cohomological automorphic representation
  `π` of `GL(n)` and its contragredient `π^∨`.

  We model `π` by its highest weight / infinitesimal character
  `λ = (λ_0, …, λ_{n-1}) ∈ ℤ^n` (a `Weight n`). The contragredient acts by
  **negating and reversing** the weight:

      (λ^∨)_i = - λ_{n-1-i}                      (`dual`)

  This file establishes the structural identities that drive the period relation:

  * `dual_involutive`     : `π^{∨∨} = π` (contragredient is an involution).
  * `dual_purity`         : the purity weight negates under contragredient.
  * `sum_dual`            : the sum of the weight negates under contragredient.
  * `periodExp_dual`      : the centered period exponent is contragredient-INVARIANT
                            — the regularity-free Betti–Whittaker period relation.
  * `dual_eq_self_iff`    : `π ≅ π^∨` (self-dual) ⇔ all purity weights vanish.

  References (external): C24 (Chen, 2024), JLS26, BW (Betti–Whittaker periods), Clo.
  Chen's relation assumes the weight is *regular* (strictly decreasing); the
  theorems below assume nothing of the kind and hold for every integer weight.

  -- !-- Lab Notes -- !--
  Hypothesis (Stage 1): the contragredient of a cohomological rep of GL(n) acts on
    the infinitesimal character by "negate-and-reverse"; the `2πi`-content of the
    Betti–Whittaker period is governed by a CENTERED linear functional of the
    weight, `e(λ) = Σ_i (2i+1-n) λ_i`, whose coefficient vector is reversal-odd.
    Conjecture: `e` is invariant under contragredient with NO regularity assumption,
    generalizing Chen.
  Experiment (Stage 2): computed n = 1..4 over small integer weights (see
    `ComputationalEvidence.md`); no counterexample. Formalized over `Fin n → ℤ`,
    proving the reversal identities by reindexing with `Fin.rev`.
  Analysis (Stage 3): the decisive fact is `coeff (rev i) = - coeff i` for the
    centered coefficient `coeff i = 2i+1-n`; combined with `dual λ i = -λ (rev i)`
    the two sign flips cancel, giving invariance. Purity negates because the two
    summands swap roles. None of this uses strict monotonicity (regularity), which
    is precisely the desired generalization of C24.
  Critique (Stage 4): the identities are genuine integer-polynomial identities, not
    vacuous — `periodExp_dual` requires a `Fin.rev` reindexing and an honest cast
    computation; `dual_eq_self_iff` is a real biconditional with both directions.
    A non-regular witness (`(1,1,0)`) shows the theorems strictly extend the
    regular-weight regime of Chen's original statement.
-/

namespace BettiWhittaker

open Finset

variable {n : ℕ}

/-- The highest weight / infinitesimal character of a cohomological representation
of `GL(n)`, recorded as an integer `n`-tuple `(λ_0, …, λ_{n-1})`. -/
abbrev Weight (n : ℕ) := Fin n → ℤ

/-- The contragredient action on weights: `(λ^∨)_i = - λ_{n-1-i}`
(negate and reverse). This models passing from `π` to `π^∨`. -/
def dual (lam : Weight n) : Weight n := fun i => - lam (Fin.rev i)

/-- The `i`-th purity-weight component `w_i(λ) = λ_i + λ_{n-1-i}`. For a *pure*
(cohomological) representation this is independent of `i`. -/
def purity (lam : Weight n) (i : Fin n) : ℤ := lam i + lam (Fin.rev i)

/-- The centered period exponent `e(λ) = Σ_i (2i + 1 - n) λ_i`, recording the power
of `2πi` occurring in the Betti–Whittaker period of `π`. The coefficient vector
`(2i+1-n)_i` is the balanced arithmetic progression `-(n-1), …, (n-1)`. -/
def periodExp (lam : Weight n) : ℤ := ∑ i : Fin n, (2 * (i : ℤ) + 1 - n) * lam i

/-
The contragredient is an involution: `π^{∨∨} ≅ π`.
-/

/-
The purity weight negates under contragredient: `w_i(λ^∨) = - w_i(λ)`.
Equivalently, if `π` is pure of weight `w` then `π^∨` is pure of weight `-w`.
-/

/-
The total weight negates under contragredient: `Σ_i (λ^∨)_i = - Σ_i λ_i`.
-/

/-
**Regularity-free Betti–Whittaker period relation.**
The centered period exponent is invariant under contragredient:
`e(λ^∨) = e(λ)`. Hence the `2πi`-content of the Betti–Whittaker period of `π`
agrees with that of `π^∨`, for *every* integer weight — with no regularity
(strict dominance) assumption, generalizing Chen's relation.
-/

/-
A representation is **self-dual** (`π ≅ π^∨`) exactly when all of its purity
weights vanish.
-/

end BettiWhittaker


