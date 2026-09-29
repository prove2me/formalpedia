-- Prove2me | solution 1 for WeilDualitySign.DualEigensystem.even_card_nonfixed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:51:33.683221+00:00
-- url     : https://prove2.me/submissions/73053542-1f1f-4449-a83b-ec7840a3fcf2

-- Sol generated from Applications/WeilDualitySign/CentralParity.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_CentralParity
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

open WeilDualitySign

/-- **Free involutions have even orbit counts.**  If `g` is an involution of the ambient
type that maps a finset `s` into itself without fixed points on `s`, then `s` has even
cardinality.  (Proved by evaluating `∏_{a ∈ s} (-1 : ℤ)` through the pairing.) -/
theorem even_card_of_free_involution {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ι)
    (hmem : ∀ a ∈ s, g a ∈ s) (hginv : ∀ a, g (g a) = a) (hfree : ∀ a ∈ s, g a ≠ a) :
    Even s.card := by
  have h1 : ∏ _a ∈ s, (-1 : ℤ) = 1 :=
    Finset.prod_involution (fun a _ => g a) (fun a _ => by norm_num)
      (fun a ha _ => hfree a ha) (fun a ha => hmem a ha) (fun a _ => hginv a)
  rw [Finset.prod_const] at h1
  rcases Nat.even_or_odd s.card with h | h
  · exact h
  · rw [h.neg_one_pow] at h1; norm_num at h1

open DualEigensystem

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem K ι)


/-! ### The central eigenvalue set is duality-stable -/




/-! ### The `ℤ/2` bridge -/




/-! ### The central point: factorisation and vanishing -/









open WeilDualitySign.DualEigensystem in
theorem solution:
    Even ((univ.filter (fun i => ¬ E.σ i = i)).card) := by
  classical
  refine even_card_of_free_involution _ (fun i => E.σ i) ?_ E.σ_involutive ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [E.σ_involutive a]
    exact fun hh => ha hh.symm
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ha
