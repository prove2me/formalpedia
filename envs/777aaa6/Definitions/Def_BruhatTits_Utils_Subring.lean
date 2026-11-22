-- Prove2me | Definitions.Def_BruhatTits_Utils_Subring
-- name    : BruhatTits_Utils_Subring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:40:25.02376+00:00
-- url     : https://prove2.me/theorems/4ac284d5-560c-422c-8fdd-2c582908d256
-- title:
--   Subring
-- statement:
--   Definitions and structural lemmas for Subring, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
set_option autoImplicit false
universe uCompat vCompat wCompat
abbrev Basis (ι : Type uCompat) (R : Type vCompat) (M : Type wCompat) [Semiring R] [AddCommMonoid M] [Module R M] := Module.Basis ι R M
namespace Basis
export Module.Basis (ofEquivFun coe_ofEquivFun mem_span mk equiv equiv_apply mem_submodule_iff' map_apply equivFun_apply repr_self equivFun_symm_apply coe_reindex)
end Basis
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
omit [DecidableEq ι]
section
variable {K : Type*} [Field K]
variable {R : Subring K} [IsFractionRing R K]
end


