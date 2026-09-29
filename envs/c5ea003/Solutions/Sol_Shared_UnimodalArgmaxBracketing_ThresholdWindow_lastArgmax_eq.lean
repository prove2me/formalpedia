-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.ThresholdWindow.lastArgmax_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:41:39.904564+00:00
-- url     : https://prove2.me/submissions/46842959-fc6c-4c16-a527-a024a9ed3e31

-- Sol generated from Shared/UnimodalArgmaxBracketing.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBracketing
/-
# Strict unimodality and the *explicit* comparison of the two bracketing degrees

Research cycle theme: *strict unimodality and the bracketing of the argmax are
theorems; the missing ingredient is the explicit comparison of the two bracketing
degrees.*

A finite positive sequence `a 0, …, a n` which is **strictly log-concave**
(`a k * a (k+2) < a (k+1)^2`) is strictly unimodal.  Its set of maximisers is an
interval `[d⁻, d⁺]`, where

* `d⁻ = firstArgmax n a` is the first index at which the sequence stops *strictly*
  rising, and
* `d⁺ = lastArgmax n a` is the first index at which the sequence starts *strictly*
  falling.

Both indices *bracket* the argmax.  The point of this file is the **explicit
comparison** of the two bracketing degrees:

`lastArgmax_le_firstArgmax_succ` :  `d⁺ ≤ d⁻ + 1`
`lastArgmax_eq_succ_iff`         :  `d⁺ = d⁻ + 1 ↔ (d⁻ < n ∧ a d⁻ = a (d⁻+1))`
`lastArgmax_sub_firstArgmax`     :  `d⁺ - d⁻ = 0` or `1`, decided by the tie.

so the gap between the two brackets is `0` or `1` and *the value `1` occurs exactly
when the peak is a two-point plateau*.

The second half instantiates this for the **binomial weights**
`a k = C(n,k) p^k q^(n-k)` (`p, q > 0`), i.e. the terms of the binomial theorem for
`(p+q)^n`.  There the two bracketing degrees become completely explicit in terms of

`θ = (n+1) * p / (p + q)` :

`binomialWeight_firstArgmax` : `d⁻ = ⌈θ⌉₊ - 1`
`binomialWeight_lastArgmax`  : `d⁺ = ⌊θ⌋₊`

and the explicit comparison of the two degrees reads

`binomialWeight_bracket_gap` : `d⁺ = d⁻ + 1 ↔ θ ∈ ℕ`,

with the arithmetic corollary (`binomialWeight_nat_bracket_gap`) that for natural
weights `p, q ≥ 1` the plateau occurs iff `(p+q) ∣ (n+1)*p`, and the classical
special case `p = q = 1` (`choose_bracket_gap`): the binomial coefficients
`C(n,k)` have a two-point plateau exactly when `n` is odd.

Everything is proved from scratch; the only external input is `Mathlib`.
-/

open Shared
open UnimodalArgmaxBracketing

attribute [local instance] Classical.propDecidable

/-! ## Strictly log-concave finite sequences -/


open StrictLogConcaveOn

variable {n : ℕ} {a : ℕ → ℝ}






/-! ## The two bracketing degrees -/



variable {n : ℕ} {a : ℕ → ℝ}








/-- Characterisation of the upper bracketing degree. -/
theorem lastArgmax_eq_of {d : ℕ} (hd : d ≤ n) (hstop : d = n ∨ a (d + 1) < a d)
    (hrise : ∀ j < d, a j ≤ a (j + 1)) : lastArgmax n a = d := by
  rw [lastArgmax, Nat.find_eq_iff]
  refine ⟨hstop, fun j hj => ?_⟩
  push_neg
  exact ⟨by omega, hrise j hj⟩


/-! ### The explicit comparison of the two bracketing degrees -/





/-! ## Strict unimodality -/








/-! ## Threshold windows: the abstract mechanism producing *explicit* brackets

In every concrete example the rise pattern of the window is governed by a single
real parameter `θ` through the criterion `a k < a (k+1) ↔ k + 1 < θ`.  Isolating this
hypothesis turns the two bracketing degrees into `⌈θ⌉₊ - 1` and `⌊θ⌋₊`, and their
comparison into the arithmetic question of whether `θ` is an integer. -/



open ThresholdWindow

variable {θ : ℝ}









open Shared.UnimodalArgmaxBracketing.ThresholdWindow in
theorem solution(h : ThresholdWindow n a θ) : lastArgmax n a = ⌊θ⌋₊ := by
  have hd : ⌊θ⌋₊ ≤ n := by
    have : ⌊θ⌋₊ < n + 1 := by
      apply (Nat.floor_lt h.pos.le).2
      push_cast
      linarith [h.lt_succ]
    omega
  refine lastArgmax_eq_of hd ?_ ?_
  · rcases eq_or_lt_of_le hd with hEq | hlt
    · exact Or.inl hEq
    · refine Or.inr (not_le.1 ?_)
      rw [h.weak_rise_iff _ hlt]
      push_neg
      exact Nat.lt_floor_add_one θ
  · intro j hj
    have hjn : j < n := lt_of_lt_of_le hj hd
    rw [h.weak_rise_iff _ hjn]
    have hle : ((j + 1 : ℕ) : ℝ) ≤ θ := (Nat.le_floor_iff h.pos.le).1 (by omega)
    push_cast at hle
    linarith
