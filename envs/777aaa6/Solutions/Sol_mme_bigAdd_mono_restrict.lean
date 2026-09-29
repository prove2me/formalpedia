-- Prove2me | solution 1 for mme_bigAdd_mono_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:32:22.506661+00:00
-- url     : https://prove2.me/submissions/69365d60-682d-453c-aed8-497f810c2145

import Definitions.Def_mme_tensor_quotient

open MME PiTensorProduct

universe u

namespace BigAddMonoRestrict

theorem add_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hf : TensorObj.Restrict X X') (hg : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.add X Y) (TensorObj.add X' Y') := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  refine ⟨fun i => LinearMap.prodMap (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => LinearMap.prodMap (f i) (g i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X'.V i) (Y'.V i)) X'.t +
       PiTensorProduct.map (fun i => LinearMap.inr K (X'.V i) (Y'.V i)) Y'.t) =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t
  have h1 :
      (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ
        LinearMap.inl K (X'.V i) (Y'.V i)) =
      (fun i => LinearMap.inl K (X.V i) (Y.V i) ∘ₗ f i) := by
    funext i
    ext x <;> simp [LinearMap.prodMap]
  have h2 :
      (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ
        LinearMap.inr K (X'.V i) (Y'.V i)) =
      (fun i => LinearMap.inr K (X.V i) (Y.V i) ∘ₗ g i) := by
    funext i
    ext x <;> simp [LinearMap.prodMap]
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp, h1, h2,
    PiTensorProduct.map_comp, PiTensorProduct.map_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hf, hg]

end BigAddMonoRestrict

theorem solution
    {K : Type u} [Field K] {d k : ℕ}
    {X Y : Fin k → TensorObj K d}
    (h : ∀ j, TensorObj.Restrict (X j) (Y j)) :
    TensorObj.Restrict (TensorObj.bigAdd X) (TensorObj.bigAdd Y) := by
  induction k with
  | zero => exact TensorObj.Restrict.refl _
  | succ k ih =>
    cases k with
    | zero =>
      change TensorObj.Restrict (X 0) (Y 0)
      exact h 0
    | succ k =>
      change TensorObj.Restrict
        (TensorObj.add (X 0) (TensorObj.bigAdd (fun i => X i.succ)))
        (TensorObj.add (Y 0) (TensorObj.bigAdd (fun i => Y i.succ)))
      exact BigAddMonoRestrict.add_restrict (h 0)
        (ih (X := fun i => X i.succ) (Y := fun i => Y i.succ)
          (fun i => h i.succ))
