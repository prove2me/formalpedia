-- Prove2me | Theorems.Thm_BruhatTits_exists_repr_inv_of_fixed
-- name    : BruhatTits.exists_repr_inv_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:38.978836+00:00
-- url     : https://prove2.me/theorems/3c7ff338-bd11-49cc-a8d8-cd9ec456566b
-- title:
--   Bruhat Tits: exists repr inv of fixed
-- statement:
--   Variant of `exists_repr_inv` where the first vertex has a fixed representative.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L68-L85
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L68-L85

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.exists_repr_inv_of_fixed (M : BruhatTits.Lattice R) (y : Vertices R) :
    ∃ (ϖ : R) (_ : Irreducible ϖ) (L : BruhatTits.Lattice R)
      (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      ⟦L⟧ = y ∧ bL 0 = ϖ ^ (inv ⟦M⟧ y) • (bM 0).val ∧ bL 1 = (bM 1).val := by sorry
