-- Prove2me | Definitions.Def_Applications_WeilDualitySign_Structure
-- name    : Applications_WeilDualitySign_Structure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:58:32.488771+00:00
-- url     : https://prove2.me/theorems/41cc41ec-e7de-4980-bdc1-12201e9c9b99
-- title:
--   Aether Catalog definitions — Applications_WeilDualitySign_Structure
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WeilDualitySign.Structure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WeilDualitySign/Structure.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
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

namespace WeilDualitySign

namespace DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `ε` is a square root of unity -/


/-! ### Direct sums -/

variable {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]

/-- The **direct sum** of two duality eigensystems of the same weight `Q`: eigenvalues
are concatenated and the duality permutations act blockwise. -/
def directSum (E : DualEigensystem K ι) (F : DualEigensystem K ι₂) (hQ : F.Q = E.Q) :
    DualEigensystem K (ι ⊕ ι₂) where
  Q := E.Q
  Q_ne_zero := E.Q_ne_zero
  α := Sum.elim E.α F.α
  σ := Equiv.sumCongr E.σ F.σ
  σ_involutive := by
    rintro (i | i)
    · simp [E.σ_involutive i]
    · simp [F.σ_involutive i]
  duality := by
    rintro (i | i)
    · simpa using E.duality i
    · simpa [hQ] using F.duality i







/-! ### Twist invariance -/

/-- The **twist** of an eigensystem by a scalar `c ≠ 0`: `(Q, α) ↦ (cQ, cα)`.  This is
the eigenvalue-model shadow of a Tate twist / normalisation change. -/
def twist (E : DualEigensystem K ι) (c : K) (hc : c ≠ 0) : DualEigensystem K ι where
  Q := c * E.Q
  Q_ne_zero := mul_ne_zero hc E.Q_ne_zero
  α := fun i => c * E.α i
  σ := E.σ
  σ_involutive := E.σ_involutive
  duality := fun i => by linear_combination c ^ 2 * E.duality i


/-! ### Odd degree -/




end DualEigensystem

end WeilDualitySign


