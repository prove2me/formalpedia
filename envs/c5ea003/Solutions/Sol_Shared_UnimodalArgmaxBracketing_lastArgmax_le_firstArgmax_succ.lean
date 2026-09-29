-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.lastArgmax_le_firstArgmax_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:43:07.829332+00:00
-- url     : https://prove2.me/submissions/045302b6-6b1b-485c-9b5b-63a5cb573fa4

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


theorem lastArgmax_le : lastArgmax n a ≤ n :=
  Nat.find_le (Or.inl rfl)


theorem weak_rise_of_lt_lastArgmax {j : ℕ} (hj : j < lastArgmax n a) : a j ≤ a (j + 1) := by
  have := Nat.find_min (p := fun k => k = n ∨ a (k + 1) < a k) ⟨n, Or.inl rfl⟩ hj
  push_neg at this
  exact this.2

theorem fall_at_firstArgmax (h : firstArgmax n a < n) :
    a (firstArgmax n a + 1) ≤ a (firstArgmax n a) := by
  rcases Nat.find_spec (p := fun k => k = n ∨ a (k + 1) ≤ a k) ⟨n, Or.inl rfl⟩ with h1 | h1
  · exact absurd h1 (Nat.ne_of_lt h)
  · exact h1





/-! ### The explicit comparison of the two bracketing degrees -/





/-! ## Strict unimodality -/








/-! ## Threshold windows: the abstract mechanism producing *explicit* brackets

In every concrete example the rise pattern of the window is governed by a single
real parameter `θ` through the criterion `a k < a (k+1) ↔ k + 1 < θ`.  Isolating this
hypothesis turns the two bracketing degrees into `⌈θ⌉₊ - 1` and `⌊θ⌋₊`, and their
comparison into the arithmetic question of whether `θ` is an integer. -/



open ThresholdWindow

variable {θ : ℝ}









open Shared in
theorem solution(h : StrictLogConcaveOn n a) :
    lastArgmax n a ≤ firstArgmax n a + 1 := by
  by_contra hcon
  push_neg at hcon
  set d := firstArgmax n a with hd
  have hdn : d + 1 < n := lt_of_lt_of_le hcon lastArgmax_le
  have hrise1 : a d ≤ a (d + 1) := weak_rise_of_lt_lastArgmax (n := n) (by omega)
  have hrise2 : a (d + 1) ≤ a (d + 2) := weak_rise_of_lt_lastArgmax (n := n) (by omega)
  have hfall : a (d + 1) ≤ a d := fall_at_firstArgmax (by omega)
  have heq : a d = a (d + 1) := le_antisymm hrise1 hfall
  have h0 : 0 < a d := h.pos d (by omega)
  have := h.newton d (by omega)
  nlinarith
