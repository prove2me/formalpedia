-- Prove2me | Theorems.Thm_WeightMonodromy_StrictFormalityData_exact_iff_mem_idl
-- name    : WeightMonodromy.StrictFormalityData.exact_iff_mem_idl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:40:48.340267+00:00
-- url     : https://prove2.me/theorems/c753b636-459c-4380-83a3-2cf6eb3b7ccc
-- title:
--   Inside `sub`, being a coboundary of `A` is exactly membership in the ideal: hence
-- statement:
--   Inside `sub`, being a coboundary of `A` is exactly membership in the ideal: hence
--   `H(A) ≅ sub / idl` as algebras, and the latter has zero differential.
--
--   ```lean
--   theorem WeightMonodromy.StrictFormalityData.exact_iff_mem_idl(z : A) (hz : z ∈ F.sub) (hdz : D.d z = 0) :
--       (∃ c : A, z = D.d c) ↔ z ∈ F.idl := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/WeightMonodromyFormality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/WeightMonodromyFormality.lean#L453

-- Thm stub generated from Novelty/WeightMonodromyFormality.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Formality of weight-graded dg-algebras (algebraic core of weight-monodromy formality)

This file formalises the algebraic mechanism behind the theorem that the étale and de Rham
cohomology algebras of a smooth proper rigid-analytic space over a finite extension of `Q_p`
are *formal* as soon as the space satisfies the weight-monodromy conjecture.

The geometric input (rigid-analytic spaces, comparison theorems, the monodromy filtration) is
not formalised here.  What *is* formalised is the purely algebraic statement that carries the
whole argument:

> A differential graded algebra equipped with an additional *weight* grading, whose cohomology
> is **pure** (the weight of a class of cohomological degree `n` equals `n`), is formal.

Weight-monodromy is exactly what guarantees purity of the weight grading in the rigid-analytic
setting; formality is then a formal consequence of purity, which is what we prove.

## Main definitions

* `WeightedDGA 𝒜` : a differential graded algebra structure on a bigraded algebra
  `𝒜 : ℤ × ℤ → Submodule k A` (first index = cohomological degree, second index = weight).
* `IsWeightPure 𝒜 D` : purity, i.e. every cocycle of bidegree `(n, w)` with `w ≠ n` is a
  coboundary of an element of the *same* weight.
* `subDGA`, `idealDGA` : the sub-dg-algebra `A'` obtained by weight-wise canonical truncation,
  and the acyclic ideal `J ⊆ A'` whose quotient is the cohomology algebra.
* `StrictFormalityData` : a strict formality zig-zag `A ⊇ A' ↠ A'/J` in which the quotient
  carries the zero differential.

## Main results

* `formality_of_weight_purity` : purity implies formality, producing an explicit
  `StrictFormalityData`.
* `StrictFormalityData.cohomology_surj` / `StrictFormalityData.exact_iff_mem_ideal` :
  the quotient `A'/J` really is the cohomology algebra of `A`.

The Massey product consequences (and the resulting obstruction to weight-monodromy for
non-formal spaces) are in `Catalog/Novelty/WeightMonodromyMassey.lean`.
-/

open WeightMonodromy

open scoped Classical

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]


variable (𝒜 : ℤ × ℤ → Submodule k A) [GradedAlgebra 𝒜]










variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜]


open WeightedDGA

variable (D : WeightedDGA 𝒜)






variable (D : WeightedDGA 𝒜)



























open StrictFormalityData

variable {D : WeightedDGA 𝒜} (F : StrictFormalityData D)

include F

theorem WeightMonodromy.StrictFormalityData.exact_iff_mem_idl(z : A) (hz : z ∈ F.sub) (hdz : D.d z = 0) :
    (∃ c : A, z = D.d c) ↔ z ∈ F.idl := by sorry
