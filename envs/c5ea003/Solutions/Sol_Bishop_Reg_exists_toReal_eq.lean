-- Prove2me | solution 1 for Bishop.Reg.exists_toReal_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:26:46.681464+00:00
-- url     : https://prove2.me/submissions/f50c6ea6-0575-411c-ae12-bf3949b6f6bb

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
theorem solution(r : ℝ) : ∃ x : Reg, x.toReal = r := by
  have hchoice : ∀ n : ℕ, ∃ q : ℚ, |r - (q : ℝ)| < 1 / (2 * (n + 1)) := by
    intro n
    exact exists_rat_near r (by positivity)
  choose q hq using hchoice
  have hreg : ∀ m n : ℕ, |q m - q n| ≤ 1 / (m + 1) + 1 / (n + 1) := by
    intro m n
    have hm := hq m
    have hn := hq n
    have : |((q m : ℝ)) - (q n : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
      have h1 : |((q m : ℝ)) - (q n : ℝ)| ≤ |(q m : ℝ) - r| + |r - (q n : ℝ)| :=
        abs_sub_le _ _ _
      have h2 : |(q m : ℝ) - r| < 1 / (2 * (m + 1)) := by
        rw [abs_sub_comm]; exact hm
      have h3 : (1 : ℝ) / (2 * (m + 1)) ≤ 1 / (m + 1) := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have h4 : (1 : ℝ) / (2 * (n + 1)) ≤ 1 / (n + 1) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have h' : ((|q m - q n| : ℚ) : ℝ) ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using this
    exact_mod_cast h'
  refine ⟨⟨q, hreg⟩, ?_⟩
  set x : Reg := ⟨q, hreg⟩ with hx
  have key : ∀ n : ℕ, |x.toReal - r| ≤ 2 / (n + 1) := by
    intro n
    have h1 := x.abs_toReal_sub_approx_le n
    have h2 := hq n
    have hxa : x.approx n = q n := rfl
    rw [hxa] at h1
    have h3 : |(q n : ℝ) - r| ≤ 1 / (n + 1) := by
      rw [abs_sub_comm]
      have h4 : (1 : ℝ) / (2 * (n + 1)) ≤ 1 / (n + 1) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [h2]
    calc |x.toReal - r| ≤ |x.toReal - (q n : ℝ)| + |(q n : ℝ) - r| := abs_sub_le _ _ _
      _ ≤ 1 / (n + 1) + 1 / (n + 1) := add_le_add h1 h3
      _ = 2 / (n + 1) := by ring
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  have h0 : |x.toReal - r| ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
  have := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  linarith [this]
