-- Prove2me | solution 1 for WeightMonodromy.massey_zero_of_formality
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:16:37.009036+00:00
-- url     : https://prove2.me/submissions/b3f0ce0d-baa2-4077-833a-26230b43fdff

-- Sol generated from Novelty/WeightMonodromyMassey.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
import Theorems.Thm_WeightMonodromy_StrictFormalityData_exact_iff_mem_idl
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Massey products, purity and the obstruction to weight-monodromy

Companion to `Catalog/Novelty/WeightMonodromyFormality.lean`.

Two complementary results are proved.

* `massey_zero_of_formality` : in any strictly formal dg-algebra (i.e. one admitting a
  `StrictFormalityData`) every triple Massey product which is defined contains `0`.  The
  mechanism is that the primitives can be chosen inside the acyclic ideal, which is absorbing.

* `massey_zero_of_weightPure` : the same conclusion directly from purity of the weight grading,
  by a *weight* argument: a Massey representative of cohomological degree `p + q + r - 1`
  necessarily has weight `p + q + r`, and purity kills everything off the diagonal.
  The primitives are moreover produced explicitly as bihomogeneous components.

* `not_weightPure_of_massey` : contrapositive.  A space whose cohomology algebra carries a
  genuinely non-vanishing triple Massey product cannot have a pure weight grading; this is the
  algebraic shadow of the non-formal rigid-analytic surfaces, which are therefore obstructions
  to the naive weight-monodromy purity in the corresponding dg-algebra model.
-/

open WeightMonodromy

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] {D : WeightedDGA 𝒜}



variable (D)






open WeightMonodromy in
theorem solution(F : StrictFormalityData D) {x y z : A}
    (hx : x ∈ F.sub) (hz : z ∈ F.sub)
    (hxy_sub : x * y ∈ F.sub) (hyz_sub : y * z ∈ F.sub)
    (hxy_d : D.d (x * y) = 0) (hyz_d : D.d (y * z) = 0)
    (hxy_ex : ∃ c, x * y = D.d c) (hyz_ex : ∃ c, y * z = D.d c) (s : k)
    (hcocycle : ∀ u v : A, D.d u = x * y → D.d v = y * z →
      D.d (s • (u * z) - x * v) = 0) :
    ∃ u v w : A, D.d u = x * y ∧ D.d v = y * z ∧ s • (u * z) - x * v = D.d w := by
  -- the primitives can be chosen inside the acyclic ideal
  have hxy_idl : x * y ∈ F.idl := (F.exact_iff_mem_idl _ hxy_sub hxy_d).mp hxy_ex
  have hyz_idl : y * z ∈ F.idl := (F.exact_iff_mem_idl _ hyz_sub hyz_d).mp hyz_ex
  obtain ⟨u, hu, hdu⟩ := F.idl_acyclic _ hxy_idl hxy_d
  obtain ⟨v, hv, hdv⟩ := F.idl_acyclic _ hyz_idl hyz_d
  -- the Massey representative lies in the ideal, hence bounds
  have hm : s • (u * z) - x * v ∈ F.idl :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (F.idl_mul u hu z hz))
      (F.mul_idl x hx v hv)
  have hmd : D.d (s • (u * z) - x * v) = 0 := hcocycle u v hdu.symm hdv.symm
  obtain ⟨w, -, hw⟩ := F.idl_acyclic _ hm hmd
  exact ⟨u, v, w, hdu.symm, hdv.symm, hw⟩
