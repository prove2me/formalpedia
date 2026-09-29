-- Prove2me | Definitions.Def_Bridges_ReedMuller_Defs
-- name    : Bridges_ReedMuller_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:26.779273+00:00
-- url     : https://prove2.me/theorems/355f1be9-8f5a-4dc1-b1e3-e84142b65fd1
-- title:
--   Aether Catalog definitions — Bridges_ReedMuller_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ReedMuller.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ReedMuller/Defs.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Basic weight definitions for generalized Reed–Muller codes

The Reed–Muller files of the catalog (`Bridges.ReedMuller.ExtremalPoly`,
`Bridges.ReedMuller.FiberRestriction`, `Bridges.ReedMuller.MinDistance`) all
speak about the *evaluation word* of a multivariate polynomial over a finite
field: the function `x ↦ eval x f` on `𝔽ⁿ`.  This file collects the two counting
functions they use, together with the elementary relations between them.

## Main definitions

- `GRM.hammingWeight f`: the number of points of `𝔽ⁿ` at which `f` does not
  vanish, i.e. the Hamming weight of the evaluation word of `f`.
- `GRM.zeroCount f`: the number of points at which `f` vanishes.

## Main results

- `GRM.hammingWeight_add_zeroCount`: the two counts add up to `qⁿ`.
- `GRM.hammingWeight_eq`: `hammingWeight f = qⁿ - zeroCount f`.
-/

open MvPolynomial Finset Fintype

namespace GRM

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-- The Hamming weight of the evaluation word of `f`: the number of points of
`𝔽ⁿ` at which `f` does not vanish. -/
noncomputable def hammingWeight {n : ℕ} (f : MvPolynomial (Fin n) 𝔽) : ℕ :=
  (Finset.univ.filter fun x : Fin n → 𝔽 => MvPolynomial.eval x f ≠ 0).card

/-- The number of points of `𝔽ⁿ` at which `f` vanishes. -/
noncomputable def zeroCount {n : ℕ} (f : MvPolynomial (Fin n) 𝔽) : ℕ :=
  (Finset.univ.filter fun x : Fin n → 𝔽 => MvPolynomial.eval x f = 0).card




end GRM


