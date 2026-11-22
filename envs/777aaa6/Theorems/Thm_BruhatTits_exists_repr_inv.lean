-- Prove2me | Theorems.Thm_BruhatTits_exists_repr_inv
-- name    : BruhatTits.exists_repr_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:12.73493+00:00
-- url     : https://prove2.me/theorems/c6c10099-996b-4fa6-85fb-8112e5462c07
-- title:
--   Bruhat Tits: exists repr inv
-- statement:
--   Given vertices `x` and `y`, there exist representatives `M` and `L` and a basis
--   `bM` of `M` such that `(ϖ ^ (inv x y) • (bM 0), bM 1)` is a basis of `L`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L89-L95
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L89-L95

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.exists_repr_inv (x y : Vertices R) :
    ∃ (ϖ : R) (_ : Irreducible ϖ) (M L : BruhatTits.Lattice R)
      (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      ⟦M⟧ = x ∧ ⟦L⟧ = y ∧ bL 0 = ϖ ^ (inv x y) • (bM 0).val ∧ bL 1 = (bM 1).val := by sorry
