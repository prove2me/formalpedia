-- Prove2me | Definitions.Def_Applications_WeilDualitySign_CentralParity
-- name    : Applications_WeilDualitySign_CentralParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:59.184444+00:00
-- url     : https://prove2.me/theorems/01d1a0aa-1a55-4be9-b6b8-2e58b700e40c
-- title:
--   Aether Catalog definitions — Applications_WeilDualitySign_CentralParity
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WeilDualitySign.CentralParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WeilDualitySign/CentralParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle 2: the sign is the parity of the central order of vanishing

`EigenvalueModel.lean` computed the functional-equation sign of a duality eigensystem as

  `ε = (−1)^{d + #neg-fixed}`.

That formula refers to the duality permutation.  This file eliminates `σ` from the answer
entirely and proves the **intrinsic** law

  `ε = (−1)^{m₊}`,   `m₊ := #{ i : α_i = Q }`,

where `m₊` is the multiplicity of the "central" eigenvalue `α = q^{n/2}`.  Since
`P(T) = ∏ (1 - α_i T)` vanishes at the central point `T = Q⁻¹` to order exactly `m₊`
(`charPoly_factor_central`, `centralFactor_ne_zero`), this says:

> **the sign of the functional equation is the parity of the order of vanishing at the
> central point** —

the exact function-field analogue of the parity statement proved analytically for
`Λ(2 - s) = w Λ(s)` in `Catalog/Applications/BSD/FunctionalEquation.lean`
(`analyticRank_parity`).  There the input was Taylor symmetry of an analytic function;
here it is a purely combinatorial pairing of Frobenius eigenvalues.  The two theorems are
the archimedean and the finite-field faces of one statement.

The bridge from cycle 1 is a `ℤ/2` count (`even_deg_add_negFixed_add_centralOrder`):
duality 2-cycles contribute evenly to *both* `d` and `m₊`, `+Q` fixed points contribute
oddly to both, and `−Q` fixed points contribute `1` to `d` and `1` to `#neg-fixed`.  The
hypothesis `−1 ≠ 1` is necessary and sharp: in characteristic `2` the two fixed-point
types coincide and the bookkeeping collapses.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): `ε` should not depend on `σ` at all — `σ` is auxiliary data,
  while the multiset `{α_i}` is intrinsic.  The only intrinsic `ℤ/2` invariant available
  is the multiplicity of the self-dual eigenvalue `+Q`.
Experiment (Experimenter): count.  Split `ι` into `Fix(σ)` and its complement `R`.  On
  `R`, `σ` is a free involution, so `|R|` is even; and `{α_i = Q}` is `σ`-stable
  (`α_i = Q ⟹ α_{σ i} = Q²/Q = Q`), so its intersection with `R` is also even.  The two
  even contributions cancel mod `2` and leave `m₊ ≡ |Fix₊|` and `d + #neg ≡ |Fix₊|`.
Analysis (Analyst): the same "free involution ⟹ even" principle is used twice, so it is
  isolated as `even_card_of_free_involution`; it is the combinatorial engine of the whole
  project (`Finset.prod_involution` over `ℤ` with constant value `−1`).
Critique (Critic): in characteristic `2` the statement `ε = (−1)^{m₊}` degenerates
  (`ε = 1` always), and the counting argument genuinely fails, so the theorems carry
  `hchar : (-1 : K) ≠ 1`.  The central factorisation, by contrast, needs no such
  hypothesis and is stated in full generality.
Synthesis (PI): cycle 1's sign law plus this parity bridge give a self-contained,
  σ-free statement of the conjecture: *no `−q^{n/2}` self-dual eigenvalue* forces
  `ε = (−1)^d`, and *always* `ε = (−1)^{ord_{T = q^{-n/2}} P}`.
-/

open Finset
open scoped Classical

namespace WeilDualitySign


namespace DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem K ι)

/-- The **central multiplicity** `m₊ = #{i : α_i = Q}`: the multiplicity of the self-dual
eigenvalue `+q^{n/2}`, equivalently the order of vanishing of `P` at `T = Q⁻¹`. -/
noncomputable def centralOrder : ℕ := by
  classical
  exact (univ.filter (fun i => E.α i = E.Q)).card

/-! ### The central eigenvalue set is duality-stable -/




/-! ### The `ℤ/2` bridge -/




/-! ### The central point: factorisation and vanishing -/

/-- The non-central part of the characteristic polynomial,
`G(T) = ∏_{α_i ≠ Q} (1 - α_i T)`. -/
noncomputable def centralFactor (T : K) : K := by
  classical
  exact ∏ i ∈ univ.filter (fun i => ¬ E.α i = E.Q), (1 - E.α i * T)






end DualEigensystem

end WeilDualitySign


