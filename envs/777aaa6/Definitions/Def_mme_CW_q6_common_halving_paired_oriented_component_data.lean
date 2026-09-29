-- Prove2me | Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
-- name    : mme_CW_q6_common_halving_paired_oriented_component_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T12:12:19.425174+00:00
-- url     : https://prove2.me/theorems/61d66420-91d2-4bee-86e9-c9fe4b0900b7
-- title:
--   Common-halving paired oriented component data
-- statement:
--   Given one primary q=6 address family and one common position halving, this module reads the first half in the twice-cyclic coupled orientation and the second half in the once-cyclic orientation. It defines the two transported gradings, the literal heterogeneous component block selected by each family entry, the exact paired address projector, and its three explicit matrix-multiplication parameters. The parameter formulas retain the per-entry rectangular shape rather than replacing it by a fixed survivor; their product will be proved separately to be the common volume 6^(4G+2L).
-- source:
--   Coppersmith--Winograd 1990, coupled constituent and induced C-tensor extraction; Duan--Wu--Zhou 2023, Section 6.3/Table 2 paired 121/211 orientations.

import Definitions.Def_mme_CW_q6_common_paired_halving
import Definitions.Def_mme_TypeGrading_permutation
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_induced_word_zeroing

open MME PiTensorProduct Module TensorProduct BigOperators

universe u

set_option autoImplicit false

namespace MME.PairedOrientedPackaging

variable {K : Type u} [Field K]
variable {N L G A H : ℕ}

/-- Matrix-multiplication parameters of one supported unpermuted coupled
block.  The two `Z = 2` blocks have shape `⟨6,1,6⟩`; the other two have
shape `⟨1,6,1⟩`. -/
def localM (sigma : Fin 3 → Fin 3) : ℕ :=
  if sigma 2 = 2 then 6 else 1

def localN (sigma : Fin 3 → Fin 3) : ℕ :=
  if sigma 2 = 2 then 1 else 6

def localP (sigma : Fin 3 → Fin 3) : ℕ :=
  if sigma 2 = 2 then 6 else 1

/-- The first half of one retained coupled address, read in the physical
mode order of the twice-cyclically permuted coupled constituent. -/
def leftAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) : Fin 3 → Fin N → Fin 3 :=
  fun i r ↦
    (family.entry p).1
      ((cyclicPerm.trans cyclicPerm).symm i)
      (halving.position (Sum.inl r))

/-- The second half of one retained coupled address, read in the physical
mode order of the once-cyclically permuted coupled constituent. -/
def rightAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) : Fin 3 → Fin N → Fin 3 :=
  fun i r ↦
    (family.entry p).1
      (cyclicPerm.symm i)
      (halving.position (Sum.inr r))

/-- The unpermuted coupled type at one position in the first half. -/
def leftType
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) (r : Fin N) : Fin 3 → Fin 3 :=
  fun i ↦ (family.entry p).1 i (halving.position (Sum.inl r))

/-- The unpermuted coupled type at one position in the second half. -/
def rightType
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) (r : Fin N) : Fin 3 → Fin 3 :=
  fun i ↦ (family.entry p).1 i (halving.position (Sum.inr r))

/-- First matrix parameter of the heterogeneous paired component.  The
twice-cyclic first half contributes its old `N` parameter, while the
once-cyclic second half contributes its old `P` parameter. -/
def componentM
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) : ℕ :=
  (∏ r : Fin N, localN (leftType family halving p r)) *
    (∏ r : Fin N, localP (rightType family halving p r))

/-- Middle matrix parameter of the heterogeneous paired component. -/
def componentN
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) : ℕ :=
  (∏ r : Fin N, localP (leftType family halving p r)) *
    (∏ r : Fin N, localM (rightType family halving p r))

/-- Third matrix parameter of the heterogeneous paired component. -/
def componentP
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) : ℕ :=
  (∏ r : Fin N, localM (leftType family halving p r)) *
    (∏ r : Fin N, localN (rightType family halving p r))

/-- The explicit coupled grading transported through the twice-cyclic mode
permutation used by the row-121 factor. -/
noncomputable def leftGrading :
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
      (coupledObj K 6)).TypeGrading 3 :=
  TensorObj.TypeGrading.permObjGrading
    (MME.DWZComponentRestriction.dwzQ6CoupledGrading K)
    (cyclicPerm.trans cyclicPerm)

/-- The explicit coupled grading transported through the once-cyclic mode
permutation used by the row-211 factor. -/
noncomputable def rightGrading :
    (TensorObj.permObj cyclicPerm (coupledObj K 6)).TypeGrading 3 :=
  TensorObj.TypeGrading.permObjGrading
    (MME.DWZComponentRestriction.dwzQ6CoupledGrading K)
    cyclicPerm

/-- The literal heterogeneous component selected by one family entry from
the paired oriented source. -/
noncomputable def componentObj
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) : TensorObj K 3 :=
  TensorObj.kron
    (gradedAddressBlock (leftGrading (K := K))
      (leftAddress family halving p))
    (gradedAddressBlock (rightGrading (K := K))
      (rightAddress family halving p))

/-- Project both oriented powers to the two half-addresses belonging to one
family entry. -/
noncomputable def componentProj
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) (i : Fin 3) :
    ((TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm
        (coupledObj K 6)).kronPow N)).V i) →ₗ[K]
      (componentObj (K := K) family halving p).V i :=
  TensorProduct.map
    (gradedAddressProj (leftGrading (K := K)) N
      (leftAddress family halving p) i)
    (gradedAddressProj (rightGrading (K := K)) N
      (rightAddress family halving p) i)

end MME.PairedOrientedPackaging


