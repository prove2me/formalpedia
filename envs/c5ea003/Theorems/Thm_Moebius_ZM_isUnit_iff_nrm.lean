-- Prove2me | Theorems.Thm_Moebius_ZM_isUnit_iff_nrm
-- name    : Moebius.ZM.isUnit_iff_nrm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:43:31.643159+00:00
-- url     : https://prove2.me/theorems/a483c368-1161-4104-8d99-2933ae874dee
-- title:
--   Units are exactly the elements of norm `±1`.
-- statement:
--   Units are exactly the elements of norm `±1`.
--
--   ```lean
--   theorem Moebius.ZM.isUnit_iff_nrm(z : ZM) : IsUnit z ↔ nrm z = 1 ∨ nrm z = -1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/MoebiusTwistRing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/MoebiusTwistRing.lean#L147

-- Thm stub generated from MachineLearning/MoebiusTwistRing.lean
import Mathlib
import Definitions.Def_MachineLearning_MoebiusTwistRing

/-!
# The Möbius Twist Ring `ZM = ℤ[t]/(t² − 1)`

This file develops the *correct* algebraic home of the "Möbius integers" idea:
the ring obtained from `ℤ` by adjoining a formal orientation-reversing symbol
`t` with `t² = 1` (the holonomy of the Möbius band's orientation double cover).

We realise `ℤ[t]/(t²−1)` concretely as the subring

  `evenDiff = {(u, v) ∈ ℤ × ℤ | u ≡ v (mod 2)}`

via `a + b·t ↦ (a + b, a − b)` (the "characters of ℤ/2" coordinates).  This gives
the `CommRing` structure for free and makes every computation transparent.

## Main results

* `ZM.mk_mul`, `ZM.mk_add` — the twisted multiplication `(a,b)(c,d) = (ac+bd, ad+bc)`.
* `ZM.tw_sq`, `ZM.isUnit_tw`, `ZM.not_prime_tw` — the twist `t` is a unit of order 2,
  hence **not** a prime: "orientation is a unit, not a prime".
* `ZM.not_domain` — `ZM` is not an integral domain: `(1+t)(1−t) = 0`.
* `ZM.nrm_mul`, `ZM.isUnit_iff_nrm`, `ZM.isUnit_mk_iff` — the norm `N(a+bt) = a² − b²`
  is multiplicative and detects units; the unit group is `{±1, ±t} ≅ (ℤ/2)²`.
* `ZM.nrm_ne_two` — no element has norm `±2`; consequently `ZM.irreducible_two`.
* `ZM.irreducible_mk_int_iff` — a rational integer is irreducible in `ZM` **iff** it is
  `±2`: the twist ring destroys the primality of every odd prime.
* `ZM.odd_prime_splits` — every odd integer `2k+1` factors nontrivially in `ZM`,
  e.g. `3 = (2 + t)(2 − t)`; so `6 = 2·(2+t)·(2−t)` has **three** irreducible factors.
* `ZM.idempotent_eq` and `ZM.not_ringEquiv_prod` — `ZM` has no nontrivial idempotents,
  hence `ZM ≇ ℤ × ℤ`: the Möbius extension of `ℤ` by its twist does not split.
* `ZM.tw_pow_eq_one_iff` — holonomy: `t^n = 1 ↔ n` even, matching `σ² = id` for the
  deck transformation `σ(x,y) = (x+1,−y)` of the Möbius band.
-/

open Moebius



open ZM

















/-! ### Failure of the domain property -/



/-! ### The norm -/

theorem Moebius.ZM.isUnit_iff_nrm(z : ZM) : IsUnit z ↔ nrm z = 1 ∨ nrm z = -1 := by sorry
