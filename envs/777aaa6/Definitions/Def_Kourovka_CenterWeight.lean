-- Prove2me | Definitions.Def_Kourovka_CenterWeight
-- name    : Kourovka_CenterWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:30:57.890727+00:00
-- url     : https://prove2.me/theorems/c4742dab-75a0-4703-8b32-c39988ee42a4
-- title:
--   Center Weight
-- statement:
--   Definitions and structural lemmas for Center Weight, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
set_option autoImplicit true
namespace Kourovka
namespace CenterWeight
variable {G H : Type*} [Group G] [Group H]
def quotientCongr (e : G ≃* H) : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro y hy
      refine ⟨e.symm y, (Subgroup.centerCongr e.symm ⟨y, hy⟩).property, ?_⟩
      exact e.apply_symm_apply y)
noncomputable def weight (G : Type*) [Group G] : ℕ :=
  SolvableWeight.weight (G ⧸ Subgroup.center G)
noncomputable def rangeCompEquiv {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hg : Function.Injective g) : f.range ≃* (g.comp f).range :=
  (f.range.equivMapOfInjective g hg).trans
    (MulEquiv.subgroupCongr (MonoidHom.map_range g f))
end CenterWeight
end Kourovka


