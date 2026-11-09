-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_two_simple_fibre_ncard
-- name    : Couret.InterIA.Fibres.two_simple_fibre_ncard
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:41.31895+00:00
-- url     : https://prove2.me/theorems/fdc48ea0-eab5-419a-bf60-f435647310a0
-- title:
--   A two-simple cyclic support has two or four square partners
-- statement:
--   Let $m>0$, $C\subseteq\mathbb Z/(2m)\mathbb Z$ have two elements and no antipodal pair, and let $a$ be such that $C$ is disjoint from $\{a,a+m\}$. Put $S=C\cup\{a,a+m\}$. The family $\mathcal F(S)$ of four-sets with the same ordered-square counts satisfies
--
--   $$|\mathcal F(S)|=2\quad\text{or}\quad|\mathcal F(S)|=4.$$
--
--   This determines the ambiguity sizes for the two-simple support case.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoSimpleFibre.lean, lines 428–444; source file SHA-256 06c3e6b8dbdb8d80fbe47dc48b06485708ba310ea7e7b7b8681b9c42b32966b7; theorem Couret.InterIA.Fibres.two_simple_fibre_ncard

import Definitions.Def_Couret_TwoSimpleFibre_28201a278c39
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_WeightedFullPosition_056084203332
import Definitions.Def_Couret_AntipodalFreeFour_f97edb479894
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Projection Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo

theorem two_simple_fibre_ncard (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    (originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)).ncard=2 ∨
      (originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)).ncard=4 := by sorry


end Couret.InterIA.Fibres
