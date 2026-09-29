-- Prove2me | Theorems.Thm_AdjSum_cycCount_eq
-- name    : AdjSum.cycCount_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:13:29.996988+00:00
-- url     : https://prove2.me/theorems/acc8adf9-122f-40fb-83cc-ab019a119025
-- title:
--   CycCount eq
-- statement:
--   Formal statement of `AdjSum.cycCount_eq` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AdjSum.cycCount_eq(s d : ℕ) :
--       (cycCount s d : ℤ) = Matrix.trace ((adjMatZ s) ^ (d + 1)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/Recurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/Recurrence.lean#L154

-- Thm stub generated from Applications/AdjacentSumPolytopes/Recurrence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# Cayley–Hamilton recurrences and the shared characteristic denominator

Building on `Applications.AdjacentSumPolytopes.Basic`, where the open and cyclic
adjacent-sum lattice counts were identified with matrix entries and traces of powers
of the `(s+1)`-state transfer matrix `adjMat s`, we deduce:

* a **linear recurrence of order `s + 2`** satisfied by *both* the open counts and the
  cyclic counts, with coefficients the coefficients of the characteristic polynomial
  of the transfer matrix (`openCount_recurrence`, `cycCount_recurrence`);
* the resulting **shared characteristic denominator** for the two generating functions
  (`openSeries_mul_charDenom_isPoly`, `cycSeries_mul_charDenom_isPoly`): multiplying
  either formal power series by the *same* reciprocal characteristic polynomial
  `charDenom s` produces a polynomial of degree `≤ s`;
* the **Jacobi derivative identity** in the two-state case (`jacobi_two_state`):
  `(∑ₙ tr(Mⁿ) Xⁿ) · det(I − XM) = 2 − tr(M)·X = 2·p(X) − X·p'(X)` for `p = det(I − XM)`,
  which is the `k = 2` instance of `∑ₙ tr(Mⁿ)Xⁿ = (k·p − X p')/p`.

The general algebraic engine (`charpoly_pow_recurrence`, `charpoly_trace_recurrence`,
`charpoly_entry_recurrence`, `coeff_mul_revDenom`) is stated for arbitrary square
matrices over a commutative ring and for arbitrary linearly recurrent sequences, so it
applies verbatim to the `(s+2)`-state matrices of the lattice-polytope model.

-- !-- Lab Notes -- !--
* **Hypothesis.** Since the open counts are bilinear-form values `1ᵀ Mᵈ 1` and the
  cyclic counts are traces `tr Mᵈ`, Cayley–Hamilton should force *both* to obey the
  characteristic recurrence, i.e. the two Ehrhart-type series share a denominator.
* **Experiment.** For `s = 2` the characteristic polynomial of `adjMat 2` is
  `X³ − 2X² − X + 1`, and indeed both `3, 6, 14, 31, 70, 157, 353, 793` (open) and
  `2, 6, 11, 26, 57, 129, 289, 650` (cyclic) satisfy `a₍ₙ₊₃₎ = 2a₍ₙ₊₂₎ + a₍ₙ₊₁₎ − aₙ`:
  `31 = 2·14 + 6 − 3`, `70 = 2·31 + 14 − 6`, `26 = 2·11 + 6 − 2`, `57 = 2·26 + 11 − 6`.
  Computed characteristic polynomials (coefficients from the top): `s = 1 : (1,−1,−1)`,
  `s = 2 : (1,−2,−1,1)`, `s = 3 : (1,−2,−3,1,1)`, `s = 4 : (1,−3,−3,4,1,−1)`,
  `s = 5 : (1,−3,−6,4,5,−1,−1)` — the signs run in a period-four pattern `+,−,−,+`.
* **Analysis.** The recurrence survives with no positivity or irreducibility
  hypotheses whatsoever: it is pure Cayley–Hamilton.  What is *not* automatic is the
  numerator, which differs between the two parity classes; the two-state Jacobi
  identity pins it down for `k = 2`.
* **Critique.** `charpoly_pow_recurrence` needs `Nontrivial R` (for
  `charpoly_natDegree_eq_dim`); over the trivial ring everything is `0` anyway.  The
  power-series lemma is stated for `k ≤ m` — for `m < k` the coefficients are exactly
  the numerator and are generally nonzero, so the bound is sharp.
-/

open AdjSum

open Finset Matrix Polynomial PowerSeries

/-! ## Generic Cayley–Hamilton recurrences -/




/-! ## Generating functions of linearly recurrent sequences -/




/-! ## The integral transfer matrix -/





/-! ## Counting functions and their common recurrence -/

theorem AdjSum.cycCount_eq(s d : ℕ) :
    (cycCount s d : ℤ) = Matrix.trace ((adjMatZ s) ^ (d + 1)) := by sorry
