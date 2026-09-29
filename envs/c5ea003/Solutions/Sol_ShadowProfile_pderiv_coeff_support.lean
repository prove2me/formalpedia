-- Prove2me | solution 1 for ShadowProfile.pderiv_coeff_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:42:18.746903+00:00
-- url     : https://prove2.me/submissions/31de8584-f3c9-4452-a299-27672e49af9d

-- Sol generated from Bridges/PosetTheory/ShadowLogConcavity.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_ShadowLogConcavity
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Shadow Log-Concavity for Polynomial Supports

This file develops a **shadow profile theory** for multivariate polynomial supports,
establishing that the sequence of shadow cardinalities satisfies log-concavity
under structural hypotheses on the support.

## Overview

Given a set `S` of exponent vectors in `ℕⁿ` (all of the same total degree `d`),
the **k-th shadow** `Sh_k(S)` consists of all vectors `β` with `|β| = d - k`
that are coordinatewise ≤ some element of `S`. The **shadow profile** is the
sequence `k ↦ |Sh_k(S)|`.

We establish:

1. **Log-concavity of binomial coefficients** as a key arithmetic ingredient.
2. **Shadow profile for the Boolean lattice**: the shadow profile of the set
   of all characteristic functions of `r`-element subsets of `[n]` equals the
   binomial coefficient sequence `k ↦ C(n, r - k)`, which is log-concave.
3. **Shadow containment**: shadows of 0-1 vectors remain 0-1.
4. **Cross-domain**: log-concave sequences yield concentration bounds.

## References

* Brändén–Huh, *Lorentzian polynomials*, Annals of Mathematics, 2020.
* Adiprasito–Huh–Katz, *Hodge theory for combinatorial geometries*, 2018.
-/

open Finset BigOperators

noncomputable section

/-! ## Log-concavity of Binomial Coefficients

This is a fundamental arithmetic fact: `C(n,k)² ≥ C(n,k-1)·C(n,k+1)`.
-/

/-
**Theorem 1: Log-concavity of binomial coefficients.**
    For `1 ≤ k` and `k + 1 ≤ n`, we have `C(n,k)² ≥ C(n,k-1) · C(n,k+1)`.

    This is the arithmetic core of shadow log-concavity. The proof uses
    the identity `C(n,k)/C(n,k-1) = (n-k+1)/k`, showing the ratio is
    decreasing in k, which is equivalent to log-concavity.
-/

/-! ## Shadow Profile via Finset Subsets

We model the support of the basis generating polynomial of the uniform matroid
using `Finset (Fin n)` — subsets of `[n]`. The k-th shadow of the set of all
`r`-element subsets consists of all `(r-k)`-element subsets that are contained
in some `r`-element subset (which is ALL `(r-k)`-element subsets).
-/

open ShadowProfile






/-! ## Shadow of the Uniform Slice -/

/-
The cardinality of the uniform slice is `C(n, r)`.
-/

/-
**Theorem 2: Shadow of the uniform slice.**
    The k-th shadow of the set of all `r`-element subsets of `[n]` is
    exactly the set of all `(r-k)`-element subsets.

    Proof sketch: Any `(r-k)`-element subset `T ⊆ [n]` can be extended to an
    `r`-element subset by adding `k` elements from `[n] \ T`. Since `r ≤ n`,
    there are enough elements available when `k ≤ r`.
-/


/-
**Theorem 3 (Main): Shadow log-concavity for the uniform matroid.**
    The shadow profile `k ↦ C(n, r - k)` is log-concave.

    This theorem instantiates the general shadow log-concavity conjecture
    for the Boolean case, which is the support of the basis generating
    polynomial of the rank-`r` uniform matroid `U_{r,n}`.
-/

/-! ## Shadow Containment Properties -/

/-
The 0-th shadow of any family is the family itself.
-/

/-
The shadow of a single set `s` of size `r` at level `k`
    has cardinality `C(r, r-k) = C(r, k)`.
-/

/-
Shadows are monotone: if `F ⊆ G` then `shadow_k(F) ⊆ shadow_k(G)`.
-/

/-! ## Cross-Domain: Concentration from Log-Concavity -/

/-
**Theorem 4: Unimodal concentration bound.**
    A finite sequence of natural numbers satisfying log-concavity
    has the property that the maximum term is at least `total / (d+1)`.
    This is a discrete pigeonhole consequence of unimodality.

    For shadow profiles, this means: if the shadow cardinality sequence
    is log-concave, then the largest shadow layer contains at least a
    `1/(d+1)` fraction of all shadow elements across all layers.
-/

/-! ## Weighted Shadow via Polynomial Derivatives

For a polynomial `f` with nonneg coefficients, the derivative transport formula
converts shadow membership into nonvanishing of iterated derivative coefficients.
The weighted shadow count integrates this with descending factorial weights.
-/


/-
**Theorem 5: Single derivative shadow bridge.**
    If the coefficient of `β` in `∂_i f` is nonzero,
    then `β + single i 1` is in the support of `f`.
    This is the fundamental link between partial differentiation
    and the combinatorial shadow operator.
-/

/-
**Theorem 6: Iterated single-direction derivative and support.**
    If the coefficient of `β` in `(∂_i)^k f` is nonzero,
    then `β + single i k` is in the support of `f`.
-/


open ShadowProfile in
theorem solution{n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (β : Fin n →₀ ℕ) (i : Fin n)
    (hcoeff : MvPolynomial.coeff β (MvPolynomial.pderiv i f) ≠ 0) :
    β + Finsupp.single i 1 ∈ f.support := by
  -- By the chain rule, the coefficient of $\beta$ in $\partial_i f$ is the coefficient of $\beta + e_i$ in $f$ multiplied by $(\beta_i + 1)$, where $e_i$ is the standard basis vector.
  have h_chain_rule : MvPolynomial.coeff β (MvPolynomial.pderiv i f) = MvPolynomial.coeff (β + Finsupp.single i 1) f * (β i + 1) := by
    have h_chain : ∀ (g : MvPolynomial (Fin n) ℝ), MvPolynomial.coeff β (MvPolynomial.pderiv i g) = MvPolynomial.coeff (β + Finsupp.single i 1) g * (β i + 1) := by
      intro g;
      induction' g using MvPolynomial.induction_on' with g h1 h2 h3 h4 h5 h6;
      · by_cases hi : i ∈ g.support <;> simp_all +decide [ MvPolynomial.pderiv_monomial ];
        · split_ifs <;> simp_all +decide [ Finsupp.ext_iff, Finsupp.single_apply ];
          grind;
        · intro h; replace h := congr_arg ( fun x => x i ) h; aesop;
      · simp_all +decide [ mul_add, add_mul ];
        ring;
    exact h_chain f;
  grind +qlia
