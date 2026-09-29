-- Prove2me | solution 1 for Bishop.Reg.limit_spec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:26:48.419218+00:00
-- url     : https://prove2.me/submissions/6f11704c-0be6-44cc-89e7-302db1f7bca6

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
theorem solution{x : ℕ → Reg} (hx : IsRegularSeqOfReals x) (k : ℕ) :
    |(limit hx).toReal - (x k).toReal| ≤ 1 / (k + 1) := by
  have key : ∀ n : ℕ, |(limit hx).toReal - (x k).toReal|
      ≤ 2 * (1 / ((n : ℝ) + 1)) + 1 / (k + 1) := by
    intro n
    have h1 := (limit hx).abs_toReal_sub_approx_le n
    have happrox : (limit hx).approx n = (x (2 * n + 1)).approx (2 * n + 1) := rfl
    rw [happrox] at h1
    have h2 := (x (2 * n + 1)).abs_toReal_sub_approx_le (2 * n + 1)
    have e1 : ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 2 := by push_cast; ring
    rw [e1] at h2
    have h3 := hx (2 * n + 1) k
    rw [e1] at h3
    have ea : (1 : ℝ) / (2 * (n : ℝ) + 2) = (1 / ((n : ℝ) + 1)) / 2 := by
      rw [div_div]; ring_nf
    rw [ea] at h2 h3
    have h4 : |(limit hx).toReal - (x k).toReal|
        ≤ |(limit hx).toReal - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)|
          + |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x k).toReal| := abs_sub_le _ _ _
    have h5 : |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x k).toReal|
        ≤ |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x (2 * n + 1)).toReal|
          + |(x (2 * n + 1)).toReal - (x k).toReal| := abs_sub_le _ _ _
    have h2' : |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x (2 * n + 1)).toReal|
        ≤ (1 / ((n : ℝ) + 1)) / 2 := by rw [abs_sub_comm]; exact h2
    linarith
  have hlim : Tendsto (fun n : ℕ => 2 * ((1 : ℝ) / (n + 1)) + 1 / (k + 1)) atTop
      (𝓝 (2 * 0 + 1 / (k + 1))) :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)).add
      tendsto_const_nhds
  have := le_of_tendsto_of_tendsto' (tendsto_const_nhds
    (x := |(limit hx).toReal - (x k).toReal|) (f := atTop (α := ℕ))) hlim key
  simpa using this
