-- Prove2me | Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
-- name    : Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:43.053512+00:00
-- url     : https://prove2.me/theorems/d90c9c78-2fd3-4024-a288-2e07d17f4678
-- title:
--   Torsion profiles of ordinary square fibres
-- statement:
--   For a finite abelian group, the ordinary profile-$j$ family consists of ordinary square fibres containing a support with exactly $j$ elements in the two-torsion subgroup.
--
--   This definition groups ordinary fibres by the profile that determines their number of zero-free members and supports the later binomial histogram formulas.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryProfiles.lean; source file SHA-256 8256c216c05e31a8b906a7995786f22d09fd15ab7049e1a9f6c0763f1c34c435

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]











/-- The true ordinary-fibre strata, defined without arbitrary
representatives. -/
def ordinaryFibresProfile (j : ℕ) : Finset (Finset (Finset G)) :=
  (ordinaryFibres : Finset (Finset (Finset G))).filter
    (fun F => ∃ S ∈ F, (S ∩ (twoTorsion : Finset G)).card = j)



end Finite
end Couret.STROBO2TORS


