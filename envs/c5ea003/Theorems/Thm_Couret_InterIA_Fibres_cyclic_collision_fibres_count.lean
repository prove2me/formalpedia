-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_cyclic_collision_fibres_count
-- name    : Couret.InterIA.Fibres.cyclic_collision_fibres_count
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:08.711189+00:00
-- url     : https://prove2.me/theorems/8b33634a-aef8-4d51-9671-6c70a85b0e22
-- title:
--   cyclic collision fibres count
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every positive natural m and finite S,T⊆ℤ/(2m)ℤ with |S|=|T|=4 and Q(S,z)=Q(T,z) for every z, the number of distinct finite sets {x,x+m}, as x ranges over the symmetric difference (S∖T)∪(T∖S), equals 4−|S∩T|. The subtraction is natural-number subtraction; here |S∩T|≤4. An empty symmetric difference is allowed.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/AntipodalFibres.lean, lines 88–96; source file SHA-256 9a1dfe7f920807e73cc1298e40bc46156ea44c37309efcb5a094afaf09a600a4; theorem Couret.InterIA.Fibres.cyclic_collision_fibres_count

import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_four_support_fibres_count
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem cyclic_collision_fibres_count (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsquare : ∀ z, Couret.InterIA.Parity.orderedSquare S z =
      Couret.InterIA.Parity.orderedSquare T z) :
    (fibres (m : ZMod (2*m)) (symmDiff S T)).card = 4-(S ∩ T).card := by sorry


end Couret.InterIA.Fibres
