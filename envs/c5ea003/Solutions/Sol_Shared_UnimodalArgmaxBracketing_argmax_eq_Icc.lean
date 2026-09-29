-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.argmax_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:47:18.431073+00:00
-- url     : https://prove2.me/submissions/72777c36-62d5-46c1-ab9e-fa35d8b9bc26

-- Sol generated from Shared/UnimodalArgmaxBracketing.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_lastArgmax_eq_succ_iff
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_lastArgmax_le_firstArgmax_succ
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_lt_value_firstArgmax_of_outside
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

theorem firstArgmax_le : firstArgmax n a ≤ n :=
  Nat.find_le (Or.inl rfl)


theorem rise_of_lt_firstArgmax {j : ℕ} (hj : j < firstArgmax n a) : a j < a (j + 1) := by
  have := Nat.find_min (p := fun k => k = n ∨ a (k + 1) ≤ a k) ⟨n, Or.inl rfl⟩ hj
  push_neg at this
  exact this.2



theorem strict_fall_at_lastArgmax (h : lastArgmax n a < n) :
    a (lastArgmax n a + 1) < a (lastArgmax n a) := by
  rcases Nat.find_spec (p := fun k => k = n ∨ a (k + 1) < a k) ⟨n, Or.inl rfl⟩ with h1 | h1
  · exact absurd h1 (Nat.ne_of_lt h)
  · exact h1



/-- The lower bracket is at most the upper bracket.  (No log-concavity needed.) -/
theorem firstArgmax_le_lastArgmax : firstArgmax n a ≤ lastArgmax n a := by
  by_contra hcon
  push_neg at hcon
  have hlt : lastArgmax n a < n := lt_of_lt_of_le hcon firstArgmax_le
  have h1 := strict_fall_at_lastArgmax (n := n) (a := a) hlt
  have h2 := rise_of_lt_firstArgmax (n := n) (a := a) hcon
  linarith

/-! ### The explicit comparison of the two bracketing degrees -/



/-- The gap of the bracket is `0` or `1`. -/
theorem lastArgmax_sub_firstArgmax (h : StrictLogConcaveOn n a) :
    lastArgmax n a - firstArgmax n a = 0 ∨ lastArgmax n a - firstArgmax n a = 1 := by
  have := firstArgmax_le_lastArgmax (n := n) (a := a)
  have := lastArgmax_le_firstArgmax_succ h
  omega


/-! ## Strict unimodality -/




/-- The two bracketing degrees carry the same value: the peak is a plateau of
length one or two. -/
theorem value_firstArgmax_eq_lastArgmax (h : StrictLogConcaveOn n a) :
    a (firstArgmax n a) = a (lastArgmax n a) := by
  rcases (lastArgmax_sub_firstArgmax h) with hgap | hgap
  · have := firstArgmax_le_lastArgmax (n := n) (a := a)
    have : firstArgmax n a = lastArgmax n a := by omega
    rw [this]
  · have hgap' : lastArgmax n a = firstArgmax n a + 1 := by
      have := firstArgmax_le_lastArgmax (n := n) (a := a); omega
    rw [hgap']
    exact ((lastArgmax_eq_succ_iff h).1 hgap').2




/-! ## Threshold windows: the abstract mechanism producing *explicit* brackets

In every concrete example the rise pattern of the window is governed by a single
real parameter `θ` through the criterion `a k < a (k+1) ↔ k + 1 < θ`.  Isolating this
hypothesis turns the two bracketing degrees into `⌈θ⌉₊ - 1` and `⌊θ⌋₊`, and their
comparison into the arithmetic question of whether `θ` is an integer. -/



open ThresholdWindow

variable {θ : ℝ}









open Shared in
theorem solution(h : StrictLogConcaveOn n a) {k : ℕ} (hk : k ≤ n) :
    a k = a (firstArgmax n a) ↔ (firstArgmax n a ≤ k ∧ k ≤ lastArgmax n a) := by
  constructor
  · intro hval
    by_contra hcon
    push_neg at hcon
    have hout : k < firstArgmax n a ∨ lastArgmax n a < k := by
      rcases lt_or_ge k (firstArgmax n a) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hcon h1)
    exact absurd hval (ne_of_lt (lt_value_firstArgmax_of_outside h hk hout))
  · rintro ⟨h1, h2⟩
    have h3 := lastArgmax_le_firstArgmax_succ h
    have : k = firstArgmax n a ∨ k = lastArgmax n a := by omega
    rcases this with rfl | rfl
    · rfl
    · exact (value_firstArgmax_eq_lastArgmax h).symm
