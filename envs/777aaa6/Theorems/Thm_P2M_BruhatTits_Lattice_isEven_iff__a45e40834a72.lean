-- Prove2me | Theorems.Thm_P2M_BruhatTits_Lattice_isEven_iff__a45e40834a72
-- name    : P2M_BruhatTits_Lattice_isEven_iff__a45e40834a72
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:42.702834+00:00
-- url     : https://prove2.me/theorems/9a64993a-a883-40d2-92ea-639f4e93ce44
-- title:
--   P2 M Bruhat Tits Lattice is Even iff  a45e40834a72: P2 M Bruhat Tits Lattice is Even iff  a45e40834a72
-- statement:
--   The P2 M Bruhat Tits Lattice is Even iff  a45e40834a72 construction uses the P2 M Bruhat Tits Lattice is Even iff  a45e40834a72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L77-L87
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L77-L87

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits.Lattice
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem P2M_BruhatTits_Lattice_isEven_iff__a45e40834a72 (L : BruhatTits.Lattice R) :
    L.IsEven ↔ ∃ (b : Basis (Fin 2) K (Fin 2 → K)),
      b.toLattice = L ∧ Even (zaddVal (R := R) b.toGeneralLinearGroup.det) := by sorry

alias «BruhatTits».«Lattice».«isEven_iff'» := P2M_BruhatTits_Lattice_isEven_iff__a45e40834a72
