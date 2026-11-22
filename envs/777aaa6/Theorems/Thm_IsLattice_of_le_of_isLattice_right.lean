-- Prove2me | Theorems.Thm_IsLattice_of_le_of_isLattice_right
-- name    : IsLattice.of_le_of_isLattice_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:20:32.343802+00:00
-- url     : https://prove2.me/theorems/86c2bdef-73a3-4f0b-871c-e3e0630f4013
-- title:
--   Is Lattice: of le of is Lattice right
-- statement:
--   The Is Lattice construction uses the of le of is Lattice right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L759-L768
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L759-L768

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise

theorem IsLattice.of_le_of_isLattice_right [IsDiscreteValuationRing R] (L : Submodule R (Fin 2 → K))
      [IsLattice L] (M : Submodule R (Fin 2 → K))
    (h₁ : M ≤ L) (h₂ : IsLocalRing.maximalIdeal R • L ≤ M) :
    IsLattice M := by sorry
