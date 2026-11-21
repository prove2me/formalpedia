-- Prove2me | Theorems.Thm_Kourovka_CentralLattice_smul_mem_torsion_iff
-- name    : Kourovka.CentralLattice.smul_mem_torsion_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:21.063252+00:00
-- url     : https://prove2.me/theorems/83d1012d-e225-4299-a165-30c7eb1d2644
-- title:
--   Central Lattice: smul mem torsion iff
-- statement:
--   The Central Lattice construction uses the smul mem torsion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean#L193-L199
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean#L193-L199

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

theorem Kourovka.CentralLattice.smul_mem_torsion_iff {d : ℤ} (hd : d ≠ 0) (x : M) :
    d • x ∈ Submodule.torsion ℤ M ↔ x ∈ Submodule.torsion ℤ M := by sorry
