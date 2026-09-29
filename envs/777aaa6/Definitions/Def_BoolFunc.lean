-- Prove2me | Definitions.Def_BoolFunc
-- name    : BoolFunc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-04-24T03:36:11.973+00:00
-- url     : https://prove2.me/theorems/acf93f4b-a07f-4aed-9259-a03494f8f0ba
-- statement:
--   Boolean functions on `n` bits: the type `(Fin n → Bool) → Bool`.

import Mathlib.Data.Fintype.Basic

/-!
# Boolean functions on the cube

The basic type of Boolean functions `f : {0,1}ⁿ → {0,1}`, used by the
sensitivity / block-sensitivity / polynomial-degree definitions and by
the Sensitivity-Conjecture chain.
-/

/-- A Boolean function on `n` bits. -/
abbrev BoolFunc (n : ℕ) : Type := (Fin n → Bool) → Bool


