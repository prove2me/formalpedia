-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_antipodal_free_four_ne_half_translate
-- name    : Couret.InterIA.Fibres.antipodal_free_four_ne_half_translate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:09.87552+00:00
-- url     : https://prove2.me/theorems/ac9f1e2e-7433-412d-94f5-55f9a8cc9af6
-- title:
--   An antipodal-free four-set differs from its half translate
-- statement:
--   Let $m\in\mathbb N$ and $S\subseteq\mathbb Z/(2m)\mathbb Z$ have four elements. Suppose $x+m\notin S$ for every $x\in S$. Then
--
--   $$S\ne S+m.$$
--
--   This ensures the two half-translation candidates are distinct.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/AntipodalFreeFour.lean, lines 42–49; source file SHA-256 7d4d6262bdcf95ddc7a9a560bac4324cde190e4dad3f7acc41bcda6a4ccb23ed; theorem Couret.InterIA.Fibres.antipodal_free_four_ne_half_translate

import Definitions.Def_Couret_AntipodalFreeFour_f97edb479894
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem antipodal_free_four_ne_half_translate (m : ℕ)
    (S : Finset (ZMod (2*m))) (hS : S.card=4) (hfree : AntipodalFree m S) :
    S ≠ S.image (fun x => x+(m : ZMod (2*m))) := by sorry




end Couret.InterIA.Fibres
