-- Prove2me | Theorems.Thm_Bishop_Reg_toReal_eq_of_approx_le
-- name    : Bishop.Reg.toReal_eq_of_approx_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:17:18.073861+00:00
-- url     : https://prove2.me/theorems/16f6942a-7e1d-4cd9-81ba-41880dd32421
-- title:
--   If the rational approximations of a Bishop real converge to `r` at the canonical
-- statement:
--   If the rational approximations of a Bishop real converge to `r` at the canonical
--   rate (up to a constant), then the Bishop real denotes `r`.
--
--   ```lean
--   theorem Bishop.Reg.toReal_eq_of_approx_le(x : Reg) (r C : ℝ)
--       (h : ∀ n : ℕ, |(x.approx n : ℝ) - r| ≤ C * (1 / ((n : ℝ) + 1))) : x.toReal = r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/BishopReals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/BishopReals.lean#L95

-- Thm stub generated from Logic/ConstructiveAnalysis/BishopReals.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
/-
# Bishop-style constructive real numbers

This file develops the elementary theory of Errett Bishop's *regular sequences of
rationals*, the standard presentation of the real numbers in constructive analysis
(Bishop–Bridges, *Constructive Analysis*, Chapter 2).

A Bishop real is a sequence `x : ℕ → ℚ` of rationals together with the **explicit
modulus** condition

  `|x m - x n| ≤ 1/(m+1) + 1/(n+1)`,

i.e. `x n` is an approximation of the number it denotes to within `1/(n+1)`.  No
appeal to a choice principle or to a modulus obtained non-effectively is needed:
the modulus of Cauchyness is built into the datum.

Main results:

* `Bishop.Reg.abs_toReal_sub_approx_le` : the classical real `toReal x` denoted by a
  regular sequence is approximated by `x.approx n` with the *explicit* error bound
  `1/(n+1)`.
* `Bishop.Reg.equiv_iff_toReal_eq` : Bishop's equality `∀ n, |x n - y n| ≤ 2/(n+1)`
  agrees with equality of the denoted classical reals; in particular it is an
  equivalence relation (a nontrivial fact constructively).
* `Bishop.Reg.exists_toReal_eq` : every classical real is denoted by a regular
  sequence (so nothing is lost by the constructive presentation).
* `Bishop.Reg.limit` : *constructive completeness*.  From a regular sequence of
  Bishop reals one builds, by an explicit diagonal formula, a Bishop real which is
  its limit, with the explicit error estimate `|lim - x k| ≤ 1/(k+1)`.
* `Bishop.equivReal` : the quotient of the Bishop reals by Bishop equality is in
  bijection with the classical reals — the comparison with classical mathematics.
-/


open Bishop

open Filter Topology


open Reg

theorem Bishop.Reg.toReal_eq_of_approx_le(x : Reg) (r C : ℝ)
    (h : ∀ n : ℕ, |(x.approx n : ℝ) - r| ≤ C * (1 / ((n : ℝ) + 1))) : x.toReal = r := by sorry
