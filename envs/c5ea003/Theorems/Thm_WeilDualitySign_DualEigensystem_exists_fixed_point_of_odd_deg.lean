-- Prove2me | Theorems.Thm_WeilDualitySign_DualEigensystem_exists_fixed_point_of_odd_deg
-- name    : WeilDualitySign.DualEigensystem.exists_fixed_point_of_odd_deg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:08:21.823227+00:00
-- url     : https://prove2.me/theorems/9922b328-061e-47b9-9554-9c4e3e4be5bc
-- title:
--   Odd degree forces a self-dual eigenvalue.
-- statement:
--   **Odd degree forces a self-dual eigenvalue.**  A duality involution on an
--   odd-dimensional cohomology has a fixed point, since the non-fixed indices pair up.
--
--   ```lean
--   theorem WeilDualitySign.DualEigensystem.exists_fixed_point_of_odd_deg(E : DualEigensystem K ι) (hodd : Odd E.deg) :
--       ∃ i, E.σ i = i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/WeilDualitySign/Structure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/WeilDualitySign/Structure.lean#L165

-- Thm stub generated from Applications/WeilDualitySign/Structure.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Definitions.Def_Applications_WeilDualitySign_Structure
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle 3: the root sign as a `μ₂`-valued invariant

Cycles 1–2 computed the functional-equation sign of a duality eigensystem,
`ε = (−1)^{d + #neg-fixed} = (−1)^{m₊}`.  This file establishes the *structural*
properties that turn `ε` into a genuine arithmetic invariant rather than a formula:

* `rootSign_sq_eq_one` — `ε` takes values in the group `μ₂ = {±1}`;
* `rootSign_directSum` — **`ε` is multiplicative under direct sums** of eigensystems,
  as are the characteristic polynomials (`charPoly_directSum`), while the degree and the
  central multiplicity are additive.  So `E ↦ ε(E)` is a monoid homomorphism from the
  additive monoid of duality eigensystems (over a fixed `Q`) to `μ₂` — the shadow of the
  fact that root numbers are multiplicative in the Grothendieck group of Galois
  representations;
* `rootSign_twist` — `ε` is invariant under the **Tate twist / rescaling**
  `(Q, α) ↦ (cQ, cα)`, so it depends only on the *normalised* eigenvalues `α_i / Q`;
* `exists_fixed_point_of_odd_deg` — in **odd degree** a duality involution always has a
  self-dual eigenvalue `α = ±Q`, so the mission hypothesis has real content exactly in
  odd degree, and
* `rootSign_eq_neg_one_pow_deg_of_odd_deg_no_neg_fixed` — under the mission hypothesis an
  odd-degree system always has `ε = −1`, i.e. **odd degree forces central vanishing**
  (`charPoly_central_vanishing_of_odd_deg`), the eigenvalue-model analogue of "root
  number `−1` ⟹ the central value vanishes".

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): if `ε` deserves the name "root number" it must be a
  homomorphism on direct sums and be insensitive to Tate twists; if either failed, the
  cycle-1 formula would be an artefact of the model rather than an invariant.
Experiment (Experimenter): direct sums are `Sum.elim` on eigenvalues and
  `Equiv.sumCongr` on the duality permutations; every claim then follows from
  `Fintype.prod_sum_type` plus the cycle-1 closed formula.  For the twist, `∏ (c α_i)`
  and `(cQ)^d` both pick up exactly `c^d`, which cancels.
Analysis (Analyst): the odd-degree corollary is the sharpest consequence: `#non-fixed`
  is even (cycle-2 lemma), so odd `d` forces `Fix(σ) ≠ ∅`; combined with the mission
  hypothesis every fixed point carries `+Q`, so the central multiplicity is odd and `P`
  vanishes at `T = Q⁻¹`.  This is precisely the "sign `−1` ⟹ vanishing" phenomenon of
  the parity conjecture, now proved in the finite-field model.
Critique (Critic): the direct-sum construction needs the *same* `Q` on both summands
  (different weights cannot be added: that would be a graded, not a direct, sum), and
  the twist needs `c ≠ 0`.  Both hypotheses are recorded explicitly.
-/

open Finset
open scoped Classical

open WeilDualitySign

open DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `ε` is a square root of unity -/


/-! ### Direct sums -/

variable {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]








/-! ### Twist invariance -/



/-! ### Odd degree -/

theorem WeilDualitySign.DualEigensystem.exists_fixed_point_of_odd_deg(E : DualEigensystem K ι) (hodd : Odd E.deg) :
    ∃ i, E.σ i = i := by sorry
