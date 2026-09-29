-- Prove2me | solution 1 for Bishop.Reg.toReal_eq_of_approx_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:27:49.357372+00:00
-- url     : https://prove2.me/submissions/236f158f-5849-4f9a-813d-2633ee936cf5

-- Sol generated from Logic/ConstructiveAnalysis/BishopReals.lean
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













/-! ## Constructive completeness

A *regular sequence of reals* is a sequence `x : ℕ → Reg` with
`|x k - x l| ≤ 1/(k+1) + 1/(l+1)`.  Bishop's completeness theorem builds its limit
by an explicit diagonal formula, together with an explicit rate of convergence. -/











open Bishop.Reg in
theorem solution(x : Reg) (r C : ℝ)
    (h : ∀ n : ℕ, |(x.approx n : ℝ) - r| ≤ C * (1 / ((n : ℝ) + 1))) : x.toReal = r := by
  have key : ∀ n : ℕ, |x.toReal - r| ≤ (1 + C) * (1 / ((n : ℝ) + 1)) := by
    intro n
    have h1 := x.abs_toReal_sub_approx_le n
    have h2 := h n
    have h3 : |x.toReal - r| ≤ |x.toReal - (x.approx n : ℝ)| + |(x.approx n : ℝ) - r| :=
      abs_sub_le _ _ _
    have h4 : (1 : ℝ) / ((n : ℝ) + 1) = 1 * (1 / ((n : ℝ) + 1)) := by ring
    rw [h4] at h1
    nlinarith [h1, h2, h3]
  have hlim : Tendsto (fun n : ℕ => (1 + C) * ((1 : ℝ) / (n + 1))) atTop (𝓝 ((1 + C) * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 + C)
  have h0 : |x.toReal - r| ≤ 0 := by
    have := le_of_tendsto_of_tendsto' (tendsto_const_nhds
      (x := |x.toReal - r|) (f := atTop (α := ℕ))) hlim key
    simpa using this
  have := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  linarith
