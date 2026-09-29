-- Prove2me | Theorems.Thm_TropicalDuality_ker_kme_eq_vanishing_support
-- name    : TropicalDuality.ker_kme_eq_vanishing_support
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:04.711023+00:00
-- url     : https://prove2.me/theorems/2698bcf9-0e2c-4abd-aba7-d2232ba2420a
-- title:
--   Kernel–support duality: The kernel of a weighted KME functional equals
-- statement:
--   **Kernel–support duality**: The kernel of a weighted KME functional equals
--   the vanishing ideal of its support.
--
--   This is the tropical/idempotent analogue of the classical measure-theoretic fact:
--   "a nonneg integral vanishes iff the function vanishes on the support of the measure".
--
--   ```lean
--   theorem TropicalDuality.ker_kme_eq_vanishing_support(w : X → S) (hbot : (⊥ : S) = (0 : S)) :
--       kmeKernel w = (vanishingIdeal (supportOfMeasure w) : Ideal (X → S)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalDuality.lean#L181

-- Thm stub generated from Bridges/TropicalDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Gelfand Reconstruction on Finite T₀ Spaces

This file establishes a finite tropical analogue of the classical Gelfand duality /
Nullstellensatz: on a finite type `X` equipped with a function semiring `X → S`
(where `S` is a nontrivial commutative semiring with no zero divisors),
we prove:

1. **Kernel–support duality for idempotent KME**: The kernel of a weighted KME functional
   equals the vanishing ideal of its support (`ker_kme_eq_vanishing_support`).

2. **Support recovery**: The support of the vanishing ideal of a set `F` recovers `F`
   (`supportOfIdeal_vanishingIdeal`).

3. **Galois anti-isomorphism**: Subsets of `X` are in order-reversing bijection with
   support-stable geometric-radical ideals of `X → S`
   (`setIdealOrderAntiIso`).

These results form the algebraic-geometric backbone for reconstructing finite spaces
from algebras of tropical/idempotent observables.
-/


open TropicalDuality

/-! ## Setup and basic definitions -/

variable {X : Type*} {S : Type*}


variable [CommSemiring S]









variable [Fintype X] [CommSemiring S] [SemilatticeSup S] [OrderBot S]






variable [CommSemiring S]






variable [DecidableEq X] [CommSemiring S] [Nontrivial S]









variable [CommSemiring S]


variable [DecidableEq X] [Nontrivial S]





variable [Fintype X] [CommSemiring S] [SemilatticeSup S] [OrderBot S]
variable [NoZeroDivisors S]

theorem TropicalDuality.ker_kme_eq_vanishing_support(w : X → S) (hbot : (⊥ : S) = (0 : S)) :
    kmeKernel w = (vanishingIdeal (supportOfMeasure w) : Ideal (X → S)) := by sorry
