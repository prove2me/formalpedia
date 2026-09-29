-- Prove2me | solution 1 for WeightMonodromy.massey_zero_of_weightPure
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:16:38.031719+00:00
-- url     : https://prove2.me/submissions/32bddc6f-1144-4ed6-92d5-c0af4790c2f8

-- Sol generated from Novelty/WeightMonodromyMassey.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
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
theorem solution(hpure : IsWeightPure D) {p q r : ℤ} {x y z : A}
    (hx : x ∈ 𝒜 (p, p)) (hy : y ∈ 𝒜 (q, q)) (hz : z ∈ 𝒜 (r, r))
    (hdx : D.d x = 0) (hdz : D.d z = 0)
    {u₀ v₀ : A} (hu₀ : D.d u₀ = x * y) (hv₀ : D.d v₀ = y * z) :
    ∃ u v c : A, D.d u = x * y ∧ D.d v = y * z ∧
      D.sgn p • (u * z) - x * v = D.d c := by
  have hxy : x * y ∈ 𝒜 (p + q, p + q) := by
    have := SetLike.mul_mem_graded hx hy
    simpa [Prod.mk_add_mk] using this
  have hyz : y * z ∈ 𝒜 (q + r, q + r) := by
    have := SetLike.mul_mem_graded hy hz
    simpa [Prod.mk_add_mk] using this
  -- bihomogeneous primitives
  set u := cmpL 𝒜 (p + q - 1, p + q) u₀ with hu_def
  set v := cmpL 𝒜 (q + r - 1, q + r) v₀ with hv_def
  have hu_mem : u ∈ 𝒜 (p + q - 1, p + q) := cmpL_mem 𝒜 u₀ _
  have hv_mem : v ∈ 𝒜 (q + r - 1, q + r) := cmpL_mem 𝒜 v₀ _
  have hdu : D.d u = x * y := by
    have h := D.cmpL_d u₀ (p + q - 1) (p + q)
    rw [show p + q - 1 + 1 = p + q from by ring] at h
    rw [hu_def, ← h, hu₀, cmpL_of_mem_same 𝒜 hxy]
  have hdv : D.d v = y * z := by
    have h := D.cmpL_d v₀ (q + r - 1) (q + r)
    rw [show q + r - 1 + 1 = q + r from by ring] at h
    rw [hv_def, ← h, hv₀, cmpL_of_mem_same 𝒜 hyz]
  -- the Massey representative, bihomogeneous of degree `p+q+r-1` and weight `p+q+r`
  have huz : u * z ∈ 𝒜 (p + q + r - 1, p + q + r) := by
    have := SetLike.mul_mem_graded hu_mem hz
    simpa [Prod.mk_add_mk, show p + q - 1 + r = p + q + r - 1 from by ring] using this
  have hxv : x * v ∈ 𝒜 (p + q + r - 1, p + q + r) := by
    have := SetLike.mul_mem_graded hx hv_mem
    simpa [Prod.mk_add_mk, show p + (q + r - 1) = p + q + r - 1 from by ring,
      show p + (q + r) = p + q + r from by ring] using this
  have hm_mem : D.sgn p • (u * z) - x * v ∈ 𝒜 (p + q + r - 1, p + q + r) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ huz) hxv
  -- it is a cocycle, by the Leibniz rule
  have hduz : D.d (u * z) = x * y * z := by
    rw [D.leibniz (p + q - 1) (p + q) u z hu_mem, hdu, hdz]
    simp
  have hdxv : D.d (x * v) = D.sgn p • (x * (y * z)) := by
    rw [D.leibniz p p x v hx, hdx, hdv]
    simp
  have hm_d : D.d (D.sgn p • (u * z) - x * v) = 0 := by
    rw [map_sub, map_smul, hduz, hdxv, mul_assoc, sub_self]
  -- purity: degree ≠ weight, so the class vanishes
  obtain ⟨c, -, hc⟩ := hpure (p + q + r - 1) (p + q + r) (by omega) _ hm_mem hm_d
  exact ⟨u, v, c, hdu, hdv, hc.symm⟩
