-- Prove2me | Definitions.Def_Kourovka_Cofinality_LatticePullback
-- name    : Kourovka_Cofinality_LatticePullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:12:07.848171+00:00
-- url     : https://prove2.me/theorems/2cbd2872-827f-4210-a974-9ef7355694d2
-- title:
--   Lattice Pullback
-- statement:
--   Definitions and structural lemmas for Lattice Pullback, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/LatticePullback.lean

import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Definitions.Def_Kourovka_Modules_LaurentAction
import Definitions.Def_Kourovka_Covers_FiniteCover
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_second_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_abelian_kernel_commutative
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_pullback_second_kernel_commutative

set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule
def freeAbelianLatticeEquiv (k : ℕ) : FreeAbelianGroup (Fin k) ≃+ Lattice k :=
  (FreeAbelianGroup.equivFinsupp (Fin k)).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin k)).toAddEquiv
def latticeProjection {k : ℕ} (R : List (FreeGroup (Fin k))) :
    pullback Abelianization.of (abelianQuotientMap R) →* Multiplicative (Lattice k) :=
  (freeAbelianLatticeEquiv k).toMultiplicative.toMonoidHom.comp
    (second Abelianization.of (abelianQuotientMap R))
theorem latticeProjection_surjective {k : ℕ} (R : List (FreeGroup (Fin k))) :
    Function.Surjective (latticeProjection R) :=
  (freeAbelianLatticeEquiv k).toMultiplicative.surjective.comp
    (second_surjective _ _ (fun x => QuotientGroup.mk_surjective x))
def latticeKernelEquiv {k : ℕ} (R : List (FreeGroup (Fin k))) :
    (latticeProjection R).ker ≃*
      (second Abelianization.of (abelianQuotientMap R)).ker where
  toFun x := ⟨x.val, by
    apply (freeAbelianLatticeEquiv k).toMultiplicative.injective
    simpa only [map_one] using x.property⟩
  invFun x := ⟨x.val, by
    change (freeAbelianLatticeEquiv k).toMultiplicative
      (second Abelianization.of (abelianQuotientMap R) x.val) = 1
    rw [show second Abelianization.of (abelianQuotientMap R) x.val = 1 from x.property,
      map_one]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
theorem lattice_kernel_commutative {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    IsMulCommutative (latticeProjection R).ker := by
  letI := abelian_kernel_commutative hG
  letI := pullback_second_kernel_commutative Abelianization.of (abelianQuotientMap R)
  let e := latticeKernelEquiv R
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact mul_comm _ _
end Kourovka.MetabelianEnumeration.CofinalCover


