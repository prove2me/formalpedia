-- Prove2me | Theorems.Thm_Couret_proper_divisor_can_have_residue_one
-- name    : Couret.proper_divisor_can_have_residue_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:15.503074+00:00
-- url     : https://prove2.me/theorems/28722c39-a330-42c6-8f67-9a8a08eece23
-- title:
--   A proper selected product can have residue one
-- statement:
--   For the two-occurrence natural word $(31,31)$, encoded modulo 30,
--
--   $$1\text{ belongs to its proper selected-product support}.$$
--
--   Indeed the code $(0,0)$ represents the identity residue. This prevents treating residue one as an automatic sign of an empty selection.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 239–243; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.proper_divisor_can_have_residue_one

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Definitions.Def_Couret_DivisorCompleteness_e4011d047800

/-!
COU-87 S2M, 2026-10-30: the exact bridge from natural divisors to the
eight-letter modulo-30 automaton. Prime occurrences need not be distinct.
No finite 147-state / 101-class table is imported here.
-/

universe v
namespace Couret



namespace Choice











end Choice

theorem proper_divisor_can_have_residue_one :
    properSupport mod30Product
      ((Word.snoc (.snoc .empty 31) 31).map encode30) (0, 0) := by sorry


end Couret
