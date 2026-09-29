-- Prove2me | Definitions.Def_mme_dwz_step1_source_address_filters
-- name    : mme_dwz_step1_source_address_filters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T21:18:26.312971+00:00
-- url     : https://prove2.me/theorems/5c577477-c14e-4434-b254-901e79f614ab
-- title:
--   DWZ Step-1 fine-word filters on source-aligned addresses
-- statement:
--   For a fixed Table-2 coarse address, define the canonical word basis in each tensor mode. An X word passes Additional Zeroing-Out Step 1 when, in every boundary component with coarse Y-index zero, its left fine grades have the prescribed complementary split histogram. A Y word passes the dual condition in components with coarse X-index zero. These predicates are the literal source-word version of the first fine-profile zeroing in DWZ Section 6.1.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1 and Claim 6.2, printed pp. 50--52 (PDF pp. 51--53), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

open MME Module

universe u

namespace MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

/-!
# Source-address bases and the paper's first fine-profile filters

The existing source-aligned object exposes only its canonical mode-2 basis.
Additional Zeroing-Out Step 1 also filters the canonical X and Y word bases.
This file records all three mode bases and the literal boundary histogram
predicates from DWZ Section 6.1.
-/

/-- Canonical square-basis words in one mode of a fixed coarse address. -/
abbrev AddressModeWord {N : ℕ} (outer : Fin N → Fin 15) (i : Fin 3) :
    Type u :=
  ∀ r : Fin N,
    DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (cwSquareBlockType
        (DWZSquare.shapeX (outer r))
        (DWZSquare.shapeY (outer r))
        (DWZSquare.shapeZ (outer r)) i)

/-- The canonical basis in an arbitrary mode of one literal Table-2
component. -/
noncomputable def canonicalComponentModeBasis
    (K : Type u) [Field K] (s : Fin 15) (i : Fin 3) :
    Basis
      (DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (cwSquareBlockType
          (DWZSquare.shapeX s)
          (DWZSquare.shapeY s)
          (DWZSquare.shapeZ s) i)) K
      ((DWZComponentRestriction.canonicalComponentBlock K s).V i) :=
  (DWZComponentRestriction.coarseClassBasis (K := K) 6 i
    (cwSquareBlockType
      (DWZSquare.shapeX s)
      (DWZSquare.shapeY s)
      (DWZSquare.shapeZ s) i)).reindex Equiv.ulift.symm

/-- The canonical recursive word basis in any mode of a source-aligned
coarse address block. -/
noncomputable def coarseAddressModeBasis
    (K : Type u) [Field K] {N : ℕ} (outer : Fin N → Fin 15)
    (i : Fin 3) :
    Basis (AddressModeWord outer i) K ((coarseAddressObj K outer).V i) := by
  unfold coarseAddressObj gradedAddressBlock coarseAddress
  exact TensorObj.kronFinModePiBasis N
    (fun r ↦ DWZComponentRestriction.canonicalComponentBlock K (outer r)) i
    (fun r ↦ canonicalComponentModeBasis K (outer r) i)

/-- Left fine grade of one coordinate in a canonical mode word. -/
def addressModeLeftGrade {N : ℕ} {outer : Fin N → Fin 15}
    {i : Fin 3} (W : AddressModeWord outer i) (t : Fin N) : Fin 3 :=
  (W t).leftGrade

/-- Right fine grade of one coordinate in a canonical mode word. -/
def addressModeRightGrade {N : ℕ} {outer : Fin N → Fin 15}
    {i : Fin 3} (W : AddressModeWord outer i) (t : Fin N) : Fin 3 :=
  (W t).rightGrade

/-- The X-word filter in Additional Zeroing-Out Step 1.  Only boundary rows
with coarse Y-index zero impose a prescribed split histogram. -/
def addressXWordPassesStep1
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (W : AddressModeWord outer 0) : Prop :=
  ∀ (s : Fin 15), DWZSquare.shapeY s = 0 → ∀ a : Fin 3,
    Fintype.card
        {t : Fin N // outer t = s ∧
          (addressModeLeftGrade W t).val + a.val = 2} =
      DWZTable2Counts.split s a * m

/-- The Y-word filter in Additional Zeroing-Out Step 1.  Only boundary rows
with coarse X-index zero impose a prescribed split histogram. -/
def addressYWordPassesStep1
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (W : AddressModeWord outer 1) : Prop :=
  ∀ (s : Fin 15), DWZSquare.shapeX s = 0 → ∀ a : Fin 3,
    Fintype.card
        {t : Fin N // outer t = s ∧
          (addressModeLeftGrade W t).val + a.val = 2} =
      DWZTable2Counts.split s a * m

end MME.DWZSourceAligned


