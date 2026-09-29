-- Prove2me | solution 1 for Bishop.Reg.equiv_iff_toReal_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:26:45.883309+00:00
-- url     : https://prove2.me/submissions/056c870f-c2d7-4b24-9258-388d27bcc4e1

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
theorem solution(x y : Reg) : Equiv x y ↔ x.toReal = y.toReal := by
  constructor
  · intro h
    have key : ∀ n : ℕ, |x.toReal - y.toReal| ≤ 4 / (n + 1) := by
      intro n
      have hxy : |(x.approx n : ℝ) - (y.approx n : ℝ)| ≤ 2 / (n + 1) := by
        have := h n
        have h' : ((|x.approx n - y.approx n| : ℚ) : ℝ) ≤ (((2 : ℚ) / (n + 1) : ℚ) : ℝ) := by
          exact_mod_cast this
        push_cast at h'
        exact h'
      have hx := x.abs_toReal_sub_approx_le n
      have hy := y.abs_toReal_sub_approx_le n
      calc |x.toReal - y.toReal|
          ≤ |x.toReal - (x.approx n : ℝ)| + |(x.approx n : ℝ) - y.toReal| :=
            abs_sub_le _ _ _
        _ ≤ |x.toReal - (x.approx n : ℝ)|
              + (|(x.approx n : ℝ) - (y.approx n : ℝ)| + |(y.approx n : ℝ) - y.toReal|) :=
            add_le_add le_rfl (abs_sub_le _ _ _)
        _ ≤ 1 / (n + 1) + (2 / (n + 1) + 1 / (n + 1)) :=
            add_le_add hx (add_le_add hxy (by rw [abs_sub_comm]; exact hy))
        _ = 4 / (n + 1) := by ring
    have hlim : Tendsto (fun n : ℕ => (4 : ℝ) / (n + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)
    have : |x.toReal - y.toReal| ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
    have : x.toReal - y.toReal = 0 := by
      have := abs_nonneg (x.toReal - y.toReal)
      have h0 : |x.toReal - y.toReal| = 0 := le_antisymm ‹|x.toReal - y.toReal| ≤ 0› this
      exact abs_eq_zero.mp h0
    linarith
  · intro h n
    have hx := x.abs_toReal_sub_approx_le n
    have hy := y.abs_toReal_sub_approx_le n
    have : |(x.approx n : ℝ) - (y.approx n : ℝ)| ≤ 2 / (n + 1) := by
      calc |(x.approx n : ℝ) - (y.approx n : ℝ)|
          ≤ |(x.approx n : ℝ) - x.toReal| + |x.toReal - (y.approx n : ℝ)| := abs_sub_le _ _ _
        _ ≤ 1 / (n + 1) + 1 / (n + 1) := by
            gcongr
            · rw [abs_sub_comm]; exact hx
            · rw [h]; exact hy
        _ = 2 / (n + 1) := by ring
    have : ((|x.approx n - y.approx n| : ℚ) : ℝ) ≤ (((2 : ℚ) / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using this
    exact_mod_cast this
