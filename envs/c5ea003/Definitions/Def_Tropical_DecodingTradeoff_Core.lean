-- Prove2me | Definitions.Def_Tropical_DecodingTradeoff_Core
-- name    : Tropical_DecodingTradeoff_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:00.582016+00:00
-- url     : https://prove2.me/theorems/b0694624-c7fc-4d8b-bddd-29cb18eed3f6
-- title:
--   Aether Catalog definitions — Tropical_DecodingTradeoff_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.DecodingTradeoff.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/DecodingTradeoff/Core.lean by skeleton subtraction
import Mathlib
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

namespace Tropical.DecodingTradeoff

variable {S : Type*} [Fintype S] [Nonempty S]

/-! ## §1. Tropical minimum and maximum -/

/-- Tropical (min-plus) sum of a finite family: the minimum. -/
def tmin (f : S → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty f

/-- The maximum of a finite family, used to build the span seminorm. -/
def tmax (f : S → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f







/-- The **span seminorm**: the projective size of a cost-to-go vector. -/
def spanSemi (v : S → ℝ) : ℝ := tmax v - tmin v




/-! ## §2. Min-plus matrices -/

/-- Min-plus action of a transfer matrix on a cost-to-go vector. -/
def mulVec (A : S → S → ℝ) (v : S → ℝ) : S → ℝ := fun a => tmin (fun b => A a b + v b)

/-- Min-plus (tropical) matrix product. -/
def mmul (A B : S → S → ℝ) : S → S → ℝ := fun a c => tmin (fun b => A a b + B b c)

/-- A matrix is *tropically stochastic* when every row has tropical sum (= minimum) `0`. -/
def Stochastic (A : S → S → ℝ) : Prop := ∀ a, tmin (A a) = 0

/-- The **diameter** of a transfer matrix: the tropical Dobrushin coefficient. -/
def diam (A : S → S → ℝ) : ℝ := tmax fun a => tmax fun a' => tmax fun b => A a b - A a' b









/-! ## §2b. The monoid of tropically stochastic matrices

Tropically stochastic matrices are closed under the min-plus product, and the diameter is
*monotone* under composition on both sides: the tropical Dobrushin coefficient of a
product never exceeds the coefficient of either factor.  This is the matrix-level
counterpart of the absorption theorem of §3. -/







/-! ## §2c. Sup-norm nonexpansiveness -/




/-! ## §3. Windows -/

/-- `windowApply A i k v` propagates the terminal cost-to-go vector `v` backwards through
the `k` transfer matrices `A i, A (i+1), …, A (i+k-1)`.  This is the *horizon-`k`*
(windowed) decoder's cost-to-go vector at stage `i`. -/
def windowApply (A : ℕ → S → S → ℝ) : ℕ → ℕ → (S → ℝ) → (S → ℝ)
  | _, 0 => fun v => v
  | i, (k + 1) => fun v => mulVec (A i) (windowApply A (i + 1) k v)






/-! ## §4. Sharpness: the tropical noise floor

The absorption theorem cannot be improved to a bound that decays with the window
length `k`.  We exhibit a two-state chain whose span is *exactly* the diameter `d`
after every positive number of steps. -/

section NoiseFloor

/-- The symmetric two-state transfer matrix with off-diagonal cost `d`. -/
def twoState (d : ℝ) : Fin 2 → Fin 2 → ℝ := fun a b => if a = b then 0 else d








end NoiseFloor

end Tropical.DecodingTradeoff


