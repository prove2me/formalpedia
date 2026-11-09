-- Prove2me | Theorems.Thm_Couret_InterIA_IntersectionThree_odd_common_part_impossible
-- name    : Couret.InterIA.IntersectionThree.odd_common_part_impossible
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:18.275849+00:00
-- url     : https://prove2.me/theorems/2f26d2a1-4c08-4d85-a4a9-9f63225226a6
-- title:
--   odd common part impossible
-- statement:
--   For every abelian group $G$ with decidable equality, write $Q_E(z)$ for the number of ordered pairs $(x,y)∈E×E$ with $x+y=z$. there are no finite subset $C⊆G$ and $a,h∈G$ satisfying all of $h≠0$, $2h=0$, $a∉C$, $a+h∉C$, $|C|≡1$ modulo $2$, and $Q_{C∪\{a\}}(z)=Q_{C∪\{a+h\}}(z)$ for every $z∈G$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/IntersectionThree.lean, lines 59–65; source file SHA-256 b3124b74c98f6b286643eb93c66bfec0060bc80c1705a4a9f43c218fe84883d2; theorem Couret.InterIA.IntersectionThree.odd_common_part_impossible

import Definitions.Def_Couret_IntersectionThree_e6b918e458b3
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
import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
import Definitions.Def_Couret_TranslationControls_1ed5eea33a54

set_option autoImplicit false
namespace Couret.InterIA.IntersectionThree
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem odd_common_part_impossible (C : Finset G) (a h : G)
    (hh : h ≠ 0) (hh2 : h+h=0) (ha : a ∉ C) (hb : a+h ∉ C)
    (hodd : C.card % 2 = 1)
    (hsquare : ∀ z, orderedSquare (insert a C) z = orderedSquare (insert (a+h) C) z) :
    False := by sorry


end Couret.InterIA.IntersectionThree
