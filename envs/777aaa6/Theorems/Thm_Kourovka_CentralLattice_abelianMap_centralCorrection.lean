-- Prove2me | Theorems.Thm_Kourovka_CentralLattice_abelianMap_centralCorrection
-- name    : Kourovka.CentralLattice.abelianMap_centralCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:35.156178+00:00
-- url     : https://prove2.me/theorems/44ade5d8-415b-4820-bafc-ae450f1472d4
-- title:
--   Central Lattice: abelian Map central Correction
-- statement:
--   The Central Lattice construction uses the abelian Map central Correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean#L319-L326
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean#L319-L326

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
variable {G : Type*} [Group G]

theorem Kourovka.CentralLattice.abelianMap_centralCorrection (u : G →* G)
    (k : Additive (Abelianization G) →ₗ[ℤ] Additive (Subgroup.center G)) :
    abelianMap (centralCorrection u (centralLift k)) = abelianMap u + centerImage.comp k := by sorry
