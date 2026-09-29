-- Prove2me | Theorems.Thm_ShadowProfile_setShadowCard_uniformSlice_logConcave
-- name    : ShadowProfile.setShadowCard_uniformSlice_logConcave
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:14.769699+00:00
-- url     : https://prove2.me/theorems/cb15a849-86a9-4aa0-b0cc-4c2041e58087
-- title:
--   SetShadowCard uniformSlice logConcave
-- statement:
--   Formal statement of `ShadowProfile.setShadowCard_uniformSlice_logConcave` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ShadowProfile.setShadowCard_uniformSlice_logConcave(n r : ℕ) (hr : r ≤ n) :
--       IsLogConcaveSeq (setShadowCard (uniformSlice n r) r) r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/ShadowLogConcavity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/ShadowLogConcavity.lean#L138

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

theorem ShadowProfile.setShadowCard_uniformSlice_logConcave(n r : ℕ) (hr : r ≤ n) :
    IsLogConcaveSeq (setShadowCard (uniformSlice n r) r) r := by sorry
