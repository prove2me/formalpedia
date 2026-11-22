-- Prove2me | Theorems.Thm_P2M_BruhatTits_Lattice_mapIntermediate_eq_span___4df1650ccb1f
-- name    : P2M_BruhatTits_Lattice_mapIntermediate_eq_span___4df1650ccb1f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:59:08.119162+00:00
-- url     : https://prove2.me/theorems/8ce250ca-808c-465d-94f5-fe22c2382d2c
-- title:
--   P2 M Bruhat Tits Lattice map Intermediate eq span   4df1650ccb1f: P2 M Bruhat Tits Lattice map Intermediate eq span   4df1650ccb1f
-- statement:
--   The P2 M Bruhat Tits Lattice map Intermediate eq span   4df1650ccb1f construction uses the P2 M Bruhat Tits Lattice map Intermediate eq span   4df1650ccb1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L463-L497
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L463-L497

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
open BruhatTits
set_option synthInstance.maxHeartbeats 30000
open IsLocalRing
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000
open Pointwise
variable [IsFractionRing R K]

theorem P2M_BruhatTits_Lattice_mapIntermediate_eq_span___4df1650ccb1f (b : Basis (Fin 2) K (Fin 2 → K)) (M : BruhatTits.Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < b.toSubmodule)
    (h2 : ϖ • b.toSubmodule < M.M)
    (h3 : M.M ≠ (b.ntwist₂ hϖ 0 1).toSubmodule) :
    ∃ (α : R), b.toLattice.mapIntermediate M =
      Submodule.span (ResidueField R)
        {α • b.toQuotient' (R := R) 0 + b.toQuotient' (R := R) 1} := by sorry

alias «BruhatTits».«Lattice».«mapIntermediate_eq_span''» := P2M_BruhatTits_Lattice_mapIntermediate_eq_span___4df1650ccb1f
