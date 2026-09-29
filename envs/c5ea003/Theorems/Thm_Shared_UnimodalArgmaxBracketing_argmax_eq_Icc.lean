-- Prove2me | Theorems.Thm_Shared_UnimodalArgmaxBracketing_argmax_eq_Icc
-- name    : Shared.UnimodalArgmaxBracketing.argmax_eq_Icc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:51:07.995003+00:00
-- url     : https://prove2.me/theorems/e3912d27-7578-411c-a225-50d7421fe6b5
-- title:
--   The maximiser set of a strictly log-concave window is the *interval between the
-- statement:
--   The maximiser set of a strictly log-concave window is the *interval between the
--   two bracketing degrees*.
--
--   ```lean
--   theorem Shared.UnimodalArgmaxBracketing.argmax_eq_Icc(h : StrictLogConcaveOn n a) {k : ℕ} (hk : k ≤ n) :
--       a k = a (firstArgmax n a) ↔ (firstArgmax n a ≤ k ∧ k ≤ lastArgmax n a) := by sorry
--   /-! ## Threshold windows: the abstract mechanism producing *explicit* brackets
--
--   In every concrete example the rise pattern of the window is governed by a single
--   real parameter `θ` through the criterion `a k < a (k+1) ↔ k + 1 < θ`.  Isolating this
--   hypothesis turns the two bracketing degrees into `⌈θ⌉₊ - 1` and `⌊θ⌋₊`, and their
--   comparison into the arithmetic question of whether `θ` is an integer. -/
--
--
--
--   open ThresholdWindow
--
--   variable {θ : ℝ}
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/UnimodalArgmaxBracketing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/UnimodalArgmaxBracketing.lean#L295

-- Thm stub generated from Shared/UnimodalArgmaxBracketing.lean
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










/-! ### The explicit comparison of the two bracketing degrees -/





/-! ## Strict unimodality -/

theorem Shared.UnimodalArgmaxBracketing.argmax_eq_Icc(h : StrictLogConcaveOn n a) {k : ℕ} (hk : k ≤ n) :
    a k = a (firstArgmax n a) ↔ (firstArgmax n a ≤ k ∧ k ≤ lastArgmax n a) := by sorry
