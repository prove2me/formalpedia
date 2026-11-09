-- Prove2me | Theorems.Thm_Couret_InterIA_IntersectionTwo_cyclic_intersection_two_nonhalf_iff_pp
-- name    : Couret.InterIA.IntersectionTwo.cyclic_intersection_two_nonhalf_iff_pp
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:37.949199+00:00
-- url     : https://prove2.me/theorems/e3311e9f-e680-436d-ba22-9294c2d58d75
-- title:
--   Non-half translation and paired differences
-- statement:
--   For every positive natural $m$ and finite subsets $S,T\subseteq\mathbb Z/(2m)\mathbb Z$ with $|S|=|T|=4$, $|S\cap T|=2$, and equal ordered-pair sum counts everywhere, $S+m\ne T$ if and only if there exist residues $a,b$ with $S\setminus T=\{a,a+m\}$ and $T\setminus S=\{b,b+m\}$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/IntersectionTwo.lean, lines 210–219; source file SHA-256 e2c77e9e622dffdbb4d1ff0106496bedf3d7a473e3aa12fb34654a7500cbc465; theorem Couret.InterIA.IntersectionTwo.cyclic_intersection_two_nonhalf_iff_pp

import Definitions.Def_Couret_IntersectionTwo_2d7b2419466c
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_IntersectionTwoAlgebra_ba9c300e13f5

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem cyclic_intersection_two_nonhalf_iff_pp (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hI : (S ∩ T).card=2) (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    S.image (fun x => x+(m : ZMod (2*m))) ≠ T ↔
      ∃ a b, S \ T=fibre (m : ZMod (2*m)) a ∧ T \ S=fibre (m : ZMod (2*m)) b := by sorry


end Couret.InterIA.IntersectionTwo
