-- Prove2me | Definitions.Def_Shared_UnimodalArgmaxBracketing
-- name    : Shared_UnimodalArgmaxBracketing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:15:15.260395+00:00
-- url     : https://prove2.me/theorems/326c1cc3-76ca-4857-9930-380c04422afc
-- title:
--   Aether Catalog definitions — Shared_UnimodalArgmaxBracketing
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.UnimodalArgmaxBracketing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/UnimodalArgmaxBracketing.lean by skeleton subtraction
import Mathlib
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

namespace Shared
namespace UnimodalArgmaxBracketing

attribute [local instance] Classical.propDecidable

/-! ## Strictly log-concave finite sequences -/

/-- A real sequence `a` is *strictly log-concave on the window* `[0, n]` if it is
positive there and satisfies the strict Newton inequality
`a k * a (k+2) < a (k+1)^2` for every admissible `k`. -/
structure StrictLogConcaveOn (n : ℕ) (a : ℕ → ℝ) : Prop where
  pos : ∀ k ≤ n, 0 < a k
  newton : ∀ k, k + 2 ≤ n → a k * a (k + 2) < a (k + 1) ^ 2

namespace StrictLogConcaveOn

variable {n : ℕ} {a : ℕ → ℝ}





end StrictLogConcaveOn

/-! ## The two bracketing degrees -/

/-- The **lower bracketing degree**: the first index `k ≤ n` at which the sequence
stops rising strictly (capped at `n`). -/
noncomputable def firstArgmax (n : ℕ) (a : ℕ → ℝ) : ℕ :=
  Nat.find (p := fun k => k = n ∨ a (k + 1) ≤ a k) ⟨n, Or.inl rfl⟩

/-- The **upper bracketing degree**: the first index `k ≤ n` at which the sequence
starts falling strictly (capped at `n`). -/
noncomputable def lastArgmax (n : ℕ) (a : ℕ → ℝ) : ℕ :=
  Nat.find (p := fun k => k = n ∨ a (k + 1) < a k) ⟨n, Or.inl rfl⟩

variable {n : ℕ} {a : ℕ → ℝ}










/-! ### The explicit comparison of the two bracketing degrees -/





/-! ## Strict unimodality -/








/-! ## Threshold windows: the abstract mechanism producing *explicit* brackets

In every concrete example the rise pattern of the window is governed by a single
real parameter `θ` through the criterion `a k < a (k+1) ↔ k + 1 < θ`.  Isolating this
hypothesis turns the two bracketing degrees into `⌈θ⌉₊ - 1` and `⌊θ⌋₊`, and their
comparison into the arithmetic question of whether `θ` is an integer. -/

/-- A *threshold window*: the window `[0, n]` rises exactly below the real threshold
`θ ∈ (0, n+1)`. -/
structure ThresholdWindow (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) : Prop where
  pos : 0 < θ
  lt_succ : θ < (n : ℝ) + 1
  rise_iff : ∀ k < n, (a k < a (k + 1) ↔ ((k : ℝ) + 1) < θ)
  weak_rise_iff : ∀ k < n, (a k ≤ a (k + 1) ↔ ((k : ℝ) + 1) ≤ θ)


namespace ThresholdWindow

variable {θ : ℝ}







end ThresholdWindow

end UnimodalArgmaxBracketing
end Shared


