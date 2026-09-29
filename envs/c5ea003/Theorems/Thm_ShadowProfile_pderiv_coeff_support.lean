-- Prove2me | Theorems.Thm_ShadowProfile_pderiv_coeff_support
-- name    : ShadowProfile.pderiv_coeff_support
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:12:48.177027+00:00
-- url     : https://prove2.me/theorems/1a1c6686-ca5a-4424-bae4-9131662409e4
-- title:
--   Pderiv coeff support
-- statement:
--   Formal statement of `ShadowProfile.pderiv_coeff_support` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ShadowProfile.pderiv_coeff_support{n : ℕ}
--       (f : MvPolynomial (Fin n) ℝ) (β : Fin n →₀ ℕ) (i : Fin n)
--       (hcoeff : MvPolynomial.coeff β (MvPolynomial.pderiv i f) ≠ 0) :
--       β + Finsupp.single i 1 ∈ f.support := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/ShadowLogConcavity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/ShadowLogConcavity.lean#L230

-- Thm stub generated from Bridges/PosetTheory/ShadowLogConcavity.lean
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

theorem ShadowProfile.pderiv_coeff_support{n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (β : Fin n →₀ ℕ) (i : Fin n)
    (hcoeff : MvPolynomial.coeff β (MvPolynomial.pderiv i f) ≠ 0) :
    β + Finsupp.single i 1 ∈ f.support := by sorry
