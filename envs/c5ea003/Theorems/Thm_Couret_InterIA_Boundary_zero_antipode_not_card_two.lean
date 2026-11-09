-- Prove2me | Theorems.Thm_Couret_InterIA_Boundary_zero_antipode_not_card_two
-- name    : Couret.InterIA.Boundary.zero_antipode_not_card_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:29.847707+00:00
-- url     : https://prove2.me/theorems/896607cf-5068-4279-a903-bce36e54c642
-- title:
--   Zero antipode fibre
-- statement:
--   In $\mathbb Z/4\mathbb Z$, the finite set $\{0,0+0\}=\{0\}$ has cardinality different from $2$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/BoundaryControls.lean, lines 29–29; source file SHA-256 897d46031b5ccf48931b00da85e634ff15cd94b3de6ba0cc723b9f0493a360ab; theorem Couret.InterIA.Boundary.zero_antipode_not_card_two

import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
import Definitions.Def_Couret_TranslationControls_1ed5eea33a54
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
namespace Couret.InterIA.Boundary
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem zero_antipode_not_card_two : (fibre (0 : ZMod 4) 0).card ≠ 2 := by sorry


end Couret.InterIA.Boundary
