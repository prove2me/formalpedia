-- Prove2me | solution 1 for P2M_iUnion__doset_cartanDiag_eq_univ_daed3a7dc61c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:45:28.249961+00:00
-- url     : https://prove2.me/submissions/7c820889-8c61-433b-a21e-a558409bdb5f

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Theorems.Thm_P2M_cartan_decomposition__b636da006c62


set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}
theorem _root_.solution : ⋃ (f : Fin k → ℤ) (_ : Antitone f),
    Doset.doset (cartanDiag ϖ hϖ f)
      (Set.range <| GL.map R.subtype)
      (Set.range <| GL.map R.subtype) = Set.univ := by
  classical
  rw [Set.iUnion₂_eq_univ_iff]
  intro g
  obtain ⟨k₁, k₂, f, hf, h⟩ := cartan_decomposition' ϖ hϖ g
  use f, hf
  rw [DoubleCoset.mem_doubleCoset]
  use k₁, ⟨k₁, rfl⟩, k₂, ⟨k₂, rfl⟩, h.symm
