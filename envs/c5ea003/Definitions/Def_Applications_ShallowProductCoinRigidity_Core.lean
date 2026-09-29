-- Prove2me | Definitions.Def_Applications_ShallowProductCoinRigidity_Core
-- name    : Applications_ShallowProductCoinRigidity_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:48.828933+00:00
-- url     : https://prove2.me/theorems/8f2f899b-a1bd-46bf-91d9-df8c109c14e7
-- title:
--   Aether Catalog definitions — Applications_ShallowProductCoinRigidity_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ShallowProductCoinRigidity.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ShallowProductCoinRigidity/Core.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# Rigidity gap for shallow product coins — the bipartite core

## Setting

Fix two finite "registers" `A` and `B` and a *resonance set* `R ⊆ A × B`.
A **coin** on a finite register is an `ℓ²`-normalised complex amplitude vector,
`∑ a, ‖f a‖² = 1`.  The **resonance amplitude** of the *product coin* `f ⊗ g` is

`bipAmp R f g = ∑ x ∈ R, f x.1 * g x.2`.

The elementary Cauchy–Schwarz bound is `‖bipAmp R f g‖² ≤ |R|`
(`bipAmp_sq_le_card`), with equality forcing the product coin to be the
normalised indicator of `R`.  The content of this file is the *quantitative*
converse:

**Main theorem** (`bipAmp_sq_gap`).  If `R` is **not** a combinatorial box, then
for *every* product coin

`‖bipAmp R f g‖² · (3|R| + 1) ≤ 3|R|²`,  i.e.  `‖A(ψ)‖² ≤ (1 - 1/(3|R|+1))·|R|`,

an explicit multiplicative deficiency depending only on `|R|`; in additive form
`‖A(ψ)‖² ≤ |R| - 2/7` (`bipAmp_sq_le_card_sub`).

Combined with the fact that a box *does* attain the optimum
(`isBox_attains`), this yields the exact dichotomy
`resonanceAmplitude_sq_eq_iff`: the optimum `|R|` is attained by a product coin
**iff** `R` is a box.

## Proof idea

Write `u = |f| ⊗ |g|` for the modulus product vector, `T = ∑_{x∈R} u x`,
`m = |R|` and `μ = T/m`.  A direct expansion gives

`∑_{x} (u x - μ·1_R x)² = 1 - T²/m`.

If `R` is not a box there are `(a,b), (a',b') ∈ R` with `(a,b') ∉ R`, and the
four points `(a,b), (a,b'), (a',b), (a',b')` are pairwise distinct.  The `2 × 2`
minor of `u` at these points vanishes (`u` has rank one), while the
corresponding minor of `μ·1_R` equals `μ²`.  Comparing the two minors through
the four deviations `e₁₁, e₁₂, e₂₁, e₂₂` and an AM–GM step
(`rankOne_minor_ineq`) gives `μ² ≤ 3(e₁₁²+e₁₂²+e₂₁²+e₂₂²) ≤ 3(1 - T²/m)`, i.e.
`T²/m² ≤ 3 - 3T²/m`, which is exactly `T²(3m+1) ≤ 3m²`.  No singular-value
theory is needed.
-/

open Finset

namespace ShallowProductCoin

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A **coin** on a finite register: an `ℓ²`-normalised complex amplitude vector. -/
def IsCoin (f : A → ℂ) : Prop := ∑ a, ‖f a‖ ^ 2 = 1

/-- The **resonance amplitude** of the product coin `f ⊗ g` against the
resonance set `R`. -/
noncomputable def bipAmp (R : Finset (A × B)) (f : A → ℂ) (g : B → ℂ) : ℂ :=
  ∑ x ∈ R, f x.1 * g x.2

/-- `R` is a **combinatorial box** (a product set): it is closed under
recombining the first coordinate of one element with the second coordinate of
another. -/
def IsBox (R : Finset (A × B)) : Prop := ∀ x ∈ R, ∀ y ∈ R, (x.1, y.2) ∈ R

/-! ### Two elementary ingredients -/



/-! ### The gap for real rank-one vectors -/


/-! ### From real rank-one vectors to complex product coins -/






/-! ### Boxes attain the optimum -/






/-! ### The dichotomy -/


end ShallowProductCoin


