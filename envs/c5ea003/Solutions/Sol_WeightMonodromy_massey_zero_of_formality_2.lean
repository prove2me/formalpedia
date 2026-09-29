-- Prove2me | solution 2 for WeightMonodromy.massey_zero_of_formality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:30:49.700999+00:00
-- url     : https://prove2.me/submissions/f38277dc-8d1d-4ad3-ac47-2442ddeb2bf5

import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality

open WeightMonodromy in
theorem solution {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] {D : WeightedDGA 𝒜}
    (F : StrictFormalityData D) {x y z : A}
    (hx : x ∈ F.sub) (hz : z ∈ F.sub)
    (hxy_sub : x * y ∈ F.sub) (hyz_sub : y * z ∈ F.sub)
    (hxy_d : D.d (x * y) = 0) (hyz_d : D.d (y * z) = 0)
    (hxy_ex : ∃ c, x * y = D.d c) (hyz_ex : ∃ c, y * z = D.d c) (s : k)
    (hcocycle : ∀ u v : A, D.d u = x * y → D.d v = y * z →
      D.d (s • (u * z) - x * v) = 0) :
    ∃ u v w : A, D.d u = x * y ∧ D.d v = y * z ∧ s • (u * z) - x * v = D.d w := by
  -- an exact cocycle of `sub` lies in the acyclic ideal
  have hidl : ∀ t ∈ F.sub, (∃ c, t = D.d c) → t ∈ F.idl := by
    rintro t ht ⟨c, hc⟩
    obtain ⟨c', hc', htc'⟩ := F.qis_inj t ht c hc
    rw [htc']
    exact F.d_sub c' hc'
  -- choose primitives inside the ideal
  obtain ⟨u, hu, hxu⟩ := F.idl_acyclic (x * y) (hidl _ hxy_sub hxy_ex) hxy_d
  obtain ⟨v, hv, hyv⟩ := F.idl_acyclic (y * z) (hidl _ hyz_sub hyz_ex) hyz_d
  -- the Massey representative lies in the ideal and is a cocycle, hence exact
  have hmem : s • (u * z) - x * v ∈ F.idl :=
    F.idl.sub_mem (F.idl.smul_mem s (F.idl_mul u hu z hz)) (F.mul_idl x hx v hv)
  obtain ⟨w, -, hw⟩ := F.idl_acyclic _ hmem (hcocycle u v hxu.symm hyv.symm)
  exact ⟨u, v, w, hxu.symm, hyv.symm, hw⟩
