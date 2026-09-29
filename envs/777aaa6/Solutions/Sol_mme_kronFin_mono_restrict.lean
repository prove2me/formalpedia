-- Prove2me | solution 1 for mme_kronFin_mono_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:08:06.549886+00:00
-- url     : https://prove2.me/submissions/b7553db9-ee9d-47c4-818c-ecc71b6a854d

import Definitions.Def_mme_kronFin_family_mode_map_basis_data

open MME MME.TensorObj
universe u

/-- Independent factor restrictions combine through the tensor product of
their mode maps, including an empty family and arbitrary tensor order. -/
theorem solution {K : Type u} [Field K] {d n : ℕ}
    {X Y : Fin n → TensorObj K d} (h : ∀ j, Restrict (X j) (Y j)) :
    Restrict (kronFin n X) (kronFin n Y) := by
  classical
  choose f hf using h
  exact ⟨kronFinFamilyModeMap n Y X f,
    kronFinFamilyModeMap_preserves_tensor Y X f hf⟩


#print axioms solution
