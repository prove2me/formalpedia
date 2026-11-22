-- Prove2me | Theorems.Thm_Matrix_map_listProd_toGL
-- name    : Matrix.map_listProd_toGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:24.353546+00:00
-- url     : https://prove2.me/theorems/88b2f4cb-5feb-4079-a910-3557d1e55776
-- title:
--   Matrix: map list Prod to GL
-- statement:
--   The Matrix construction uses the map list Prod to GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L130-L134
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L130-L134

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R] [DecidableEq m] [DecidableEq n] [Fintype n] [Fintype m]
variable {S : Type*} [CommRing S] {F : Type*} (f : R →+* S)

theorem Matrix.map_listProd_toGL : (L : List (GL n R)) →
    (List.prod (List.map (fun g ↦ g.val.map f) L)) = (List.prod L).val.map f
  := by sorry
