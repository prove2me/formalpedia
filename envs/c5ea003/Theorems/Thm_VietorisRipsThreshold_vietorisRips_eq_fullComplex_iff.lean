-- Prove2me | Theorems.Thm_VietorisRipsThreshold_vietorisRips_eq_fullComplex_iff
-- name    : VietorisRipsThreshold.vietorisRips_eq_fullComplex_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:03:13.858018+00:00
-- url     : https://prove2.me/theorems/a625883e-794c-4515-8c24-08fa9148c26d
-- title:
--   Vietoris–Rips completion threshold.
-- statement:
--   **Vietoris–Rips completion threshold.** The Vietoris–Rips complex at scale `ε`
--   equals the full complex iff every pair of points of `α` is at distance `≤ ε`.
--
--   ```lean
--   theorem VietorisRipsThreshold.vietorisRips_eq_fullComplex_iff(ε : ℝ) :
--       (vietorisRips ε : SimpleComplex α) = fullComplex α ↔ ∀ x y : α, dist x y ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTheory/VietorisRipsThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTheory/VietorisRipsThreshold.lean#L63

-- Thm stub generated from Geometry/PosetTheory/VietorisRipsThreshold.lean
import Mathlib
import Definitions.Def_Geometry_PosetTheory_VietorisRipsThreshold

/-!
# Vietoris–Rips completion threshold

This file formalizes the *completion threshold* for the Vietoris–Rips complex of a
(pseudo)metric space.

We use a lightweight, custom notion of a downward-closed family of finite subsets
(`SimpleComplex`) rather than Mathlib's abstract simplicial complexes, in order to keep
the development self-contained and the proofs robust.

## Main definitions

* `SimpleComplex α` : a set of finite subsets ("faces") closed under taking subsets.
* `fullComplex α`   : the complex whose faces are *all* finite subsets of `α`.
* `vietorisRips ε`  : the Vietoris–Rips complex at scale `ε`; a finite subset is a face
  iff all pairwise distances of its vertices are `≤ ε`.

## Main results

* `mem_fullComplex` / `mem_vietorisRips_iff` : membership characterizations.
* `vietorisRips_eq_fullComplex_iff` :
  `vietorisRips ε = fullComplex α ↔ ∀ x y, dist x y ≤ ε`.
* `vietorisRips_eq_fullComplex_iff_sup'_le` : the finite "maximum pairwise distance"
  packaging of the above when `α` is a finite, nonempty type.
-/

open VietorisRipsThreshold


variable {α : Type*}



variable [PseudoMetricSpace α]

theorem VietorisRipsThreshold.vietorisRips_eq_fullComplex_iff(ε : ℝ) :
    (vietorisRips ε : SimpleComplex α) = fullComplex α ↔ ∀ x y : α, dist x y ≤ ε := by sorry
