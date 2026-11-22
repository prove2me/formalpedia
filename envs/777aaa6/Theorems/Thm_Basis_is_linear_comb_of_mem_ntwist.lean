-- Prove2me | Theorems.Thm_Basis_is_linear_comb_of_mem_ntwist
-- name    : Basis.is_linear_comb_of_mem_ntwist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:14:36.388974+00:00
-- url     : https://prove2.me/theorems/48cbbb86-8013-4f7e-b530-17ee89e25b63
-- title:
--   Basis: is linear comb of mem ntwist
-- statement:
--   The Basis construction uses the is linear comb of mem ntwist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L689-L702
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L689-L702

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
variable [IsFractionRing R K]

theorem Basis.is_linear_comb_of_mem_ntwist (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) (y : b.toSubmodule (R := R)) {n m : ℕ}
    (hy : y.val ∈ (b.ntwist₂ hϖ n m).toSubmodule (R := R)) :
    ∃ (α β : R),
      y = (α • (ϖ ^ n • b.restrict (R := R) 0 : b.toSubmodule (R := R))) +
        β • ϖ ^ m • b.restrict (R := R) 1 := by sorry
