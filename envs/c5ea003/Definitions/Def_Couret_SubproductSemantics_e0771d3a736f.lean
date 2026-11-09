-- Prove2me | Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
-- name    : Couret_SubproductSemantics_e0771d3a736f
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:57.026507+00:00
-- url     : https://prove2.me/theorems/e18dabf7-791d-4769-a052-e01aacb655b1
-- title:
--   Word subproducts and their mask iteration
-- statement:
--   A finite word of residue codes has a length and a selected-product support, recording nonempty choices of positions. The mask update adds the appended singleton and its products with existing selected products, and iteration yields the subproduct mask of a word. These definitions support the finite rank proof for repeated prime factors modulo 30.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/SubproductSemantics.lean; source file SHA-256 ba13bc319dc0b6baacbd98ea26d1e89628af10edec99409e87d0f01ff3d4e21c

import Std
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

def length {α : Type} : Word α → Nat
  | .empty => 0
  | .snoc w _ => length w + 1

def selectedSupport (w : Word Code30) (u : Code30) : Prop :=
  ∃ s : Choice w, s.picked ∧ Choice.eval mod30Product s = u

def subStep (m : Nat) (g : Code30) : Nat :=
  m ||| shiftMask g m ||| singletonMask g

def subRun : Word Code30 → Nat
  | .empty => 0
  | .snoc w g => subStep (subRun w) g











end S5
end Couret


