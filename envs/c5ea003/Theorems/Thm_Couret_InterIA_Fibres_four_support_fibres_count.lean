-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_four_support_fibres_count
-- name    : Couret.InterIA.Fibres.four_support_fibres_count
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:21.060125+00:00
-- url     : https://prove2.me/theorems/9418e5a2-4115-4b12-a44b-a7f93fe04536
-- title:
--   four support fibres count
-- statement:
--   Let G be any additive commutative group with decidable equality. For every h∈G with h≠0 and 2h=0 and every finite S,T⊆G with |S|=|T|=4, if every x in the symmetric difference D=(S∖T)∪(T∖S) also satisfies x+h∈D, then the number of distinct finite sets {x,x+h} for x∈D equals 4−|S∩T|. The subtraction is natural-number subtraction and |S∩T|≤4. D may be empty.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/AntipodalFibres.lean, lines 68–86; source file SHA-256 9a1dfe7f920807e73cc1298e40bc46156ea44c37309efcb5a094afaf09a600a4; theorem Couret.InterIA.Fibres.four_support_fibres_count

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
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem four_support_fibres_count (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (S T : Finset G) (hS : S.card=4) (hT : T.card=4)
    (hstable : ∀ x ∈ symmDiff S T, x+h ∈ symmDiff S T) :
    (fibres h (symmDiff S T)).card = 4-(S ∩ T).card := by sorry




end Couret.InterIA.Fibres
