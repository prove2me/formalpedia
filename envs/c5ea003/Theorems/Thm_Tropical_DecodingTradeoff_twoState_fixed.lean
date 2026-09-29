-- Prove2me | Theorems.Thm_Tropical_DecodingTradeoff_twoState_fixed
-- name    : Tropical.DecodingTradeoff.twoState_fixed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:34.871314+00:00
-- url     : https://prove2.me/theorems/3c429b3f-447f-4fd0-81ac-0ad006193622
-- title:
--   The vector `![0, d]` is a fixed point of the two-state min-plus propagation.
-- statement:
--   The vector `![0, d]` is a fixed point of the two-state min-plus propagation.
--
--   ```lean
--   theorem Tropical.DecodingTradeoff.twoState_fixed{d : ℝ} (hd : 0 ≤ d) : mulVec (twoState d) ![0, d] = ![0, d] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/DecodingTradeoff/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/DecodingTradeoff/Core.lean#L370

-- Thm stub generated from Tropical/DecodingTradeoff/Core.lean
import Mathlib
import Definitions.Def_Tropical_DecodingTradeoff_Core
/-
# Tropical Span Contraction: the algebraic endpoint of the decoding trade-off

This file develops the *algebraic* half of a cost / failure-probability trade-off for
min-plus (tropical) decoders on a chain (a trellis).

## Setting

Fix a finite nonempty state space `S`. A *tropical transfer matrix* is a function
`A : S → S → ℝ`, acting on cost-to-go vectors by the min-plus rule

  `(A ⊗ v) a = min_b (A a b + v b)`.

A matrix is **tropically stochastic** (`Stochastic`) when every row has minimum `0`;
this is the min-plus analogue of a row-stochastic matrix and is obtained from an
arbitrary matrix by subtracting row minima, an operation that changes neither the
decoder's decisions nor the argmin structure.

The relevant "distance to a constant" is the **span seminorm**
`spanSemi v = max v - min v`, which is exactly the projective quantity a min-plus
decoder is sensitive to (adding a constant to `v` changes no decision).

## Main results

* `spanSemi_mulVec_le` — min-plus propagation is *nonexpansive* for the span seminorm
  (this needs tropical stochasticity).
* `spanSemi_mulVec_le_diam` — a **Dobrushin/Doeblin-type contraction bound**: one
  min-plus step compresses the span below the matrix *diameter* `diam A`,
  *independently of the input vector*. This holds with no hypothesis on `A` at all.
* `mulVec_mmul` — associativity of the min-plus action (the tropical semiring law).
* `spanSemi_windowApply_le_diam` — **absorption theorem**: after a window of `k`
  transfer steps, the span of the propagated vector is at most `diam (A (i+j))`
  for *any* single index `j < k` inside the window; i.e. it is bounded by the
  running minimum of the diameters over the window.
* `tropicalNoiseFloor` — **sharpness**: a two-state example in which the span is
  *exactly* `d` after every positive number of steps.  Hence min-plus memory loss is
  "one-step absorption to the diameter", **not** geometric decay: purely algebraic
  arguments can never produce a bound decaying in the window length `k`.

The last two results are the structural reason why the exponential-in-window-length
failure bound of `Tropical.DecodingTradeoff.Tradeoff` *must* come from probabilistic
independence rather than from tropical algebra.
-/


open Finset

open Tropical.DecodingTradeoff

variable {S : Type*} [Fintype S] [Nonempty S]

/-! ## §1. Tropical minimum and maximum -/













/-! ## §2. Min-plus matrices -/













/-! ## §2b. The monoid of tropically stochastic matrices

Tropically stochastic matrices are closed under the min-plus product, and the diameter is
*monotone* under composition on both sides: the tropical Dobrushin coefficient of a
product never exceeds the coefficient of either factor.  This is the matrix-level
counterpart of the absorption theorem of §3. -/







/-! ## §2c. Sup-norm nonexpansiveness -/




/-! ## §3. Windows -/







/-! ## §4. Sharpness: the tropical noise floor

The absorption theorem cannot be improved to a bound that decays with the window
length `k`.  We exhibit a two-state chain whose span is *exactly* the diameter `d`
after every positive number of steps. -/

theorem Tropical.DecodingTradeoff.twoState_fixed{d : ℝ} (hd : 0 ≤ d) : mulVec (twoState d) ![0, d] = ![0, d] := by sorry
