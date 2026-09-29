-- Prove2me | solution 1 for WeilDualitySign.DualEigensystem.charPoly_central_eq_zero_of_rootSign_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T21:58:25.948621+00:00
-- url     : https://prove2.me/submissions/d3f44821-44bd-4246-8304-025580ad0790

-- Sol generated from Applications/WeilDualitySign/CentralParity.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Theorems.Thm_WeilDualitySign_DualEigensystem_rootSign_eq_neg_one_pow_centralOrder
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

open WeilDualitySign


open DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem K ι)


/-! ### The central eigenvalue set is duality-stable -/




/-! ### The `ℤ/2` bridge -/




/-! ### The central point: factorisation and vanishing -/


/-- **Central factorisation.**  `P(T) = (1 - Q T)^{m₊} · G(T)`: the characteristic
polynomial splits off exactly `m₊` copies of the central factor. -/
theorem charPoly_factor_central (T : K) :
    E.charPoly T = (1 - E.Q * T) ^ E.centralOrder * E.centralFactor T := by
  classical
  rw [charPoly, centralFactor, centralOrder,
    ← Finset.prod_filter_mul_prod_filter_not (univ : Finset ι) (fun i => E.α i = E.Q)]
  congr 1
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun i hi => by
    simp only [Finset.mem_filter] at hi
    rw [hi.2]


/-- **Function-field parity conjecture (eigenvalue model).**  The root sign is `−1`
exactly when the characteristic polynomial vanishes at the central point to *odd* order;
in particular sign `−1` forces central vanishing `P(Q⁻¹) = 0`, and sign `+1` forbids odd
vanishing.  This is the finite-field mirror of the analytic parity theorem
`BSD.FunctionalEquation.analyticRank_parity`. -/
theorem rootSign_neg_one_iff_odd_centralOrder (hchar : (-1 : K) ≠ 1) :
    E.rootSign = -1 ↔ Odd E.centralOrder := by
  rw [E.rootSign_eq_neg_one_pow_centralOrder hchar]
  constructor
  · intro h
    rcases Nat.even_or_odd E.centralOrder with he | ho
    · rw [he.neg_one_pow] at h
      exact absurd h.symm (by simpa using hchar)
    · exact ho
  · intro h
    exact h.neg_one_pow





open WeilDualitySign.DualEigensystem
open WeilDualitySign.DualEigensystem
namespace WeilDualitySign.DualEigensystem
theorem rootSign_neg_one_iff_odd_centralOrder (hchar : (-1 : K) ≠ 1) :
    E.rootSign = -1 ↔ Odd E.centralOrder := by
  rw [E.rootSign_eq_neg_one_pow_centralOrder hchar]
  constructor
  · intro h
    rcases Nat.even_or_odd E.centralOrder with he | ho
    · rw [he.neg_one_pow] at h
      exact absurd h.symm (by simpa using hchar)
    · exact ho
  · intro h
    exact h.neg_one_pow

end WeilDualitySign.DualEigensystem

namespace WeilDualitySign.DualEigensystem
theorem charPoly_factor_central (T : K) :
    E.charPoly T = (1 - E.Q * T) ^ E.centralOrder * E.centralFactor T := by
  classical
  rw [charPoly, centralFactor, centralOrder,
    ← Finset.prod_filter_mul_prod_filter_not (univ : Finset ι) (fun i => E.α i = E.Q)]
  congr 1
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun i hi => by
    simp only [Finset.mem_filter] at hi
    rw [hi.2]

end WeilDualitySign.DualEigensystem

open WeilDualitySign in
theorem solution(hchar : (-1 : K) ≠ 1)
    (h : E.rootSign = -1) : E.charPoly E.Q⁻¹ = 0 := by
  have hodd : Odd E.centralOrder := (E.rootSign_neg_one_iff_odd_centralOrder hchar).mp h
  have hpos : 0 < E.centralOrder := hodd.pos
  rw [E.charPoly_factor_central]
  have h1 : (1 : K) - E.Q * E.Q⁻¹ = 0 := by
    rw [mul_inv_cancel₀ E.Q_ne_zero, sub_self]
  rw [h1, zero_pow (by omega), zero_mul]
