-- Prove2me | solution 1 for VietorisRipsThreshold.vietorisRips_eq_fullComplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:55.216561+00:00
-- url     : https://prove2.me/submissions/8c436142-40b6-47d8-838b-abbd6d484b82

-- Sol generated from Geometry/PosetTheory/VietorisRipsThreshold.lean
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


@[simp]
theorem mem_fullComplex (s : Finset α) : s ∈ (fullComplex α).faces := Set.mem_univ s

variable [PseudoMetricSpace α]


@[simp]
theorem mem_vietorisRips_iff {ε : ℝ} (s : Finset α) :
    s ∈ (vietorisRips ε).faces ↔ ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε := Iff.rfl




open VietorisRipsThreshold in
theorem solution(ε : ℝ) :
    (vietorisRips ε : SimpleComplex α) = fullComplex α ↔ ∀ x y : α, dist x y ≤ ε := by
  classical
  constructor
  · intro h x y
    have hmem : ({x, y} : Finset α) ∈ (vietorisRips ε).faces := by
      rw [h]; exact mem_fullComplex _
    exact (mem_vietorisRips_iff _).1 hmem x (by simp) y (by simp)
  · intro h
    ext s
    simp only [mem_vietorisRips_iff, mem_fullComplex, iff_true]
    intro x _ y _
    exact h x y
