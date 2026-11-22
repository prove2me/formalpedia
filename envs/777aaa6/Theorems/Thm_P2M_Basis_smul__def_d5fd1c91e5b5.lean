-- Prove2me | Theorems.Thm_P2M_Basis_smul__def_d5fd1c91e5b5
-- name    : P2M_Basis_smul__def_d5fd1c91e5b5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:18:25.404195+00:00
-- url     : https://prove2.me/theorems/7c0e8bd2-993a-4eee-9e45-eaf3a52f53b2
-- title:
--   P2 M Basis smul  def d5fd1c91e5b5: P2 M Basis smul  def d5fd1c91e5b5
-- statement:
--   The P2 M Basis smul  def d5fd1c91e5b5 construction uses the P2 M Basis smul  def d5fd1c91e5b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L469-L469
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L469-L469

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [Fintype ι]

theorem P2M_Basis_smul__def_d5fd1c91e5b5 (a : Kˣ) (b : Basis ι K (ι → K)) : a • b = b.twist' (fun _ ↦ a) := by sorry

alias «Basis».«smul'_def» := P2M_Basis_smul__def_d5fd1c91e5b5
