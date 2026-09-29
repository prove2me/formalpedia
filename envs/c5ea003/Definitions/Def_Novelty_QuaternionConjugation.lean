-- Prove2me | Definitions.Def_Novelty_QuaternionConjugation
-- name    : Novelty_QuaternionConjugation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:07.537778+00:00
-- url     : https://prove2.me/theorems/90e884a8-d790-4ff7-8dd5-3f54a7527121
-- title:
--   Aether Catalog definitions — Novelty_QuaternionConjugation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.QuaternionConjugation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/QuaternionConjugation.lean by skeleton subtraction
import Mathlib

/-!
# Norm rigidity of quaternion conjugation

This file addresses the algebraic core of **Conjecture 5** of the
"Composition-Algebra Playground" research direction.

For a nonzero quaternion `q`, the conjugation map `x ↦ q * x * q⁻¹` preserves the
quaternionic norm for **every** `x` — not merely for unit `q`, and not merely on
the unit sphere.  This is the computation underlying the classical covers
`S³ → SO(3)` and `S³ × S³ → SO(4)`: because norm-preservation holds for all
nonzero `q`, the action factors through the projective unit group.

Everything follows from the multiplicativity of `Quaternion.normSq`
(it is a `MonoidWithZeroHom`) together with `map_inv₀`.
-/

open Quaternion

namespace QuaternionConjugation

variable {R : Type*} [CommRing R]

/-- Quaternion conjugation by a nonzero `q`. -/
noncomputable def conj (q x : ℍ[ℝ]) : ℍ[ℝ] := q * x * q⁻¹






end QuaternionConjugation


