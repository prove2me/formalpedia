-- Prove2me | Theorems.Thm_Submodule_span_eq_top_of_rank
-- name    : Submodule.span_eq_top_of_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:56:23.714321+00:00
-- url     : https://prove2.me/theorems/abd1b4ec-6269-4c8d-a3cc-b001a08ea542
-- title:
--   Submodule: span eq top of rank
-- statement:
--   The Submodule construction uses the span eq top of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L275-L289
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L275-L289

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
variable [IsFractionRing R K]
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
variable [Fintype ι]
omit [IsPrincipalIdealRing ↥R]

theorem Submodule.span_eq_top_of_rank {M : Submodule R (ι → K)} (h : Module.rank R M = Fintype.card ι) :
    Submodule.span K (M : Set (ι → K)) = ⊤ := by sorry
