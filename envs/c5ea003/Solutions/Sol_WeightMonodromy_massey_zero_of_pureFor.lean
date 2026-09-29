-- Prove2me | solution 1 for WeightMonodromy.massey_zero_of_pureFor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:16:37.546039+00:00
-- url     : https://prove2.me/submissions/49ae4cb7-38cc-4c41-8133-c6baee41c45d

-- Sol generated from Novelty/WeightMonodromyScaled.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
import Definitions.Def_Novelty_WeightMonodromyScaled
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Formality for arbitrary weight normalisations

`Catalog/Novelty/WeightMonodromyFormality.lean` proves that a weight-graded dg-algebra whose
cohomology is pure *with weight equal to the cohomological degree* is formal.  In arithmetic
practice the normalisation varies: with Tate twists the interesting weight of `H^n` is `2n`
rather than `n`, and comparison isomorphisms may rescale weights by any fixed positive factor.

This file removes the normalisation.  Fix an additive map `wt : ℤ →+ ℤ` with `0 < wt 1`
(equivalently `wt n = α n` with `α > 0`) and call a weight-graded dg-algebra `wt`-pure if its
cohomology in bidegree `(n, w)` vanishes for `w ≠ wt n`.  The main theorem
`formality_of_pureFor` produces the same strict formality zig-zag `A ⊇ A' ↠ A'/J` in this
generality, with `A'` the weight-wise canonical truncation *along the line `w = wt n`*.

The case `wt = id` recovers `formality_of_weight_purity` (see `isPureFor_id_iff`).

Note that when `α > 1` the line `w = wt n` misses most weights: for a weight `w` outside the
image of `wt` the whole weight-`w` subcomplex is acyclic and the truncation must discard it
entirely.  This is why the pieces below are indexed by pairs *(degree, diagonal index)* rather
than by bidegrees.
-/

open WeightMonodromy

open scoped Classical

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜]


variable (wt : ℤ →+ ℤ)





variable (D : WeightedDGA 𝒜) (wt : ℤ →+ ℤ)

















/-! ### Multiplicative structure -/









/-! ### Componentwise detection -/





/-! ### The main theorem -/





open WeightMonodromy in
theorem solution(hwt : 0 < wt 1) (hpure : IsPureFor D wt) {p q r : ℤ} {x y z : A}
    (hx : x ∈ 𝒜 (p, wt p)) (hy : y ∈ 𝒜 (q, wt q)) (hz : z ∈ 𝒜 (r, wt r))
    (hdx : D.d x = 0) (hdz : D.d z = 0)
    {u₀ v₀ : A} (hu₀ : D.d u₀ = x * y) (hv₀ : D.d v₀ = y * z) :
    ∃ u v c : A, D.d u = x * y ∧ D.d v = y * z ∧
      D.sgn p • (u * z) - x * v = D.d c := by
  have hxy : x * y ∈ 𝒜 (p + q, wt (p + q)) := by
    have := SetLike.mul_mem_graded hx hy
    simpa [Prod.mk_add_mk, map_add] using this
  have hyz : y * z ∈ 𝒜 (q + r, wt (q + r)) := by
    have := SetLike.mul_mem_graded hy hz
    simpa [Prod.mk_add_mk, map_add] using this
  set u := cmpL 𝒜 (p + q - 1, wt (p + q)) u₀ with hu_def
  set v := cmpL 𝒜 (q + r - 1, wt (q + r)) v₀ with hv_def
  have hu_mem : u ∈ 𝒜 (p + q - 1, wt (p + q)) := cmpL_mem 𝒜 u₀ _
  have hv_mem : v ∈ 𝒜 (q + r - 1, wt (q + r)) := cmpL_mem 𝒜 v₀ _
  have hdu : D.d u = x * y := by
    have h := D.cmpL_d u₀ (p + q - 1) (wt (p + q))
    rw [show p + q - 1 + 1 = p + q from by ring] at h
    rw [hu_def, ← h, hu₀, cmpL_of_mem_same 𝒜 hxy]
  have hdv : D.d v = y * z := by
    have h := D.cmpL_d v₀ (q + r - 1) (wt (q + r))
    rw [show q + r - 1 + 1 = q + r from by ring] at h
    rw [hv_def, ← h, hv₀, cmpL_of_mem_same 𝒜 hyz]
  have huz : u * z ∈ 𝒜 (p + q + r - 1, wt (p + q + r)) := by
    have h := SetLike.mul_mem_graded hu_mem hz
    have he : ((p + q - 1 : ℤ), wt (p + q)) + ((r : ℤ), wt r)
        = ((p + q + r - 1 : ℤ), wt (p + q + r)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]; ring
      · simp only [Prod.snd_add, ← map_add]
    rwa [he] at h
  have hxv : x * v ∈ 𝒜 (p + q + r - 1, wt (p + q + r)) := by
    have h := SetLike.mul_mem_graded hx hv_mem
    have he : ((p : ℤ), wt p) + ((q + r - 1 : ℤ), wt (q + r))
        = ((p + q + r - 1 : ℤ), wt (p + q + r)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]; ring
      · simp only [Prod.snd_add, ← map_add]
        congr 1
        ring
    rwa [he] at h
  have hm_mem : D.sgn p • (u * z) - x * v ∈ 𝒜 (p + q + r - 1, wt (p + q + r)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ huz) hxv
  have hduz : D.d (u * z) = x * y * z := by
    rw [D.leibniz (p + q - 1) (wt (p + q)) u z hu_mem, hdu, hdz]
    simp
  have hdxv : D.d (x * v) = D.sgn p • (x * (y * z)) := by
    rw [D.leibniz p (wt p) x v hx, hdx, hdv]
    simp
  have hm_d : D.d (D.sgn p • (u * z) - x * v) = 0 := by
    rw [map_sub, map_smul, hduz, hdxv, mul_assoc, sub_self]
  have hne : wt (p + q + r) ≠ wt (p + q + r - 1) := by
    intro hcon
    have := wt_injective wt hwt hcon
    omega
  obtain ⟨c, -, hc⟩ := hpure (p + q + r - 1) (wt (p + q + r)) hne _ hm_mem hm_d
  exact ⟨u, v, c, hdu, hdv, hc.symm⟩
