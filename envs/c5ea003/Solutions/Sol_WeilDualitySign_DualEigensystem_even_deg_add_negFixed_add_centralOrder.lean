-- Prove2me | solution 1 for WeilDualitySign.DualEigensystem.even_deg_add_negFixed_add_centralOrder
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:53:57.324321+00:00
-- url     : https://prove2.me/submissions/5abbe740-3a54-4651-a10f-e5d623e9fda9

-- Sol generated from Applications/WeilDualitySign/CentralParity.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Theorems.Thm_WeilDualitySign_DualEigensystem_even_card_nonfixed
import Theorems.Thm_WeilDualitySign_DualEigensystem_even_card_nonfixed_central
import Theorems.Thm_WeilDualitySign_DualEigensystem_fixed_alpha_eq_pos_or_neg
import Theorems.Thm_WeilDualitySign_DualEigensystem_mem_negFixed
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









open WeilDualitySign.DualEigensystem in
theorem solution(hchar : (-1 : K) ≠ 1) :
    Even (E.deg + E.negFixed.card + E.centralOrder) := by
  classical
  have hQne : E.Q ≠ -E.Q := by
    intro h
    apply hchar
    have h2 : (2 : K) * E.Q = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linear_combination -h3
    · exact absurd h3 E.Q_ne_zero
  -- split the index set into fixed and non-fixed indices
  have hsplit : (univ.filter (fun i => E.σ i = i)).card
      + (univ.filter (fun i => ¬ E.σ i = i)).card = E.deg := by
    rw [Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
      (p := fun i => E.σ i = i)]
    simp [deg]
  -- split the fixed indices according to the sign of their eigenvalue
  have hNF : E.negFixed = univ.filter (fun i => E.σ i = i ∧ ¬ E.α i = E.Q) := by
    ext i
    simp only [E.mem_negFixed, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h2]
      intro h3
      exact hQne h3.symm
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (E.fixed_alpha_eq_pos_or_neg h1).resolve_left h2⟩
  have hfix : (univ.filter (fun i => E.σ i = i ∧ E.α i = E.Q)).card
      + E.negFixed.card = (univ.filter (fun i => E.σ i = i)).card := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := univ.filter (fun i => E.σ i = i)) (p := fun i => E.α i = E.Q)
    rw [Finset.filter_filter, Finset.filter_filter] at hc
    rw [hNF]
    exact hc
  -- split the central set according to fixedness
  have hcentral : (univ.filter (fun i => E.σ i = i ∧ E.α i = E.Q)).card
      + (univ.filter (fun i => ¬ E.σ i = i ∧ E.α i = E.Q)).card = E.centralOrder := by
    rw [centralOrder, ← Finset.card_union_of_disjoint (s := univ.filter
        (fun i => E.σ i = i ∧ E.α i = E.Q))
      (t := univ.filter (fun i => ¬ E.σ i = i ∧ E.α i = E.Q)) ?_]
    · congr 1
      ext i
      by_cases h : E.σ i = i <;> simp [h]
    · refine Finset.disjoint_left.mpr ?_
      intro a ha hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hb.1 ha.1
  obtain ⟨k, hk⟩ := E.even_card_nonfixed
  obtain ⟨l, hl⟩ := E.even_card_nonfixed_central
  refine ⟨(univ.filter (fun i => E.σ i = i ∧ E.α i = E.Q)).card + E.negFixed.card + k + l, ?_⟩
  omega
