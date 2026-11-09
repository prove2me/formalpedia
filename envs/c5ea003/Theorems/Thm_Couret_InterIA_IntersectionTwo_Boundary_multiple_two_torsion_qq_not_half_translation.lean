-- Prove2me | Theorems.Thm_Couret_InterIA_IntersectionTwo_Boundary_multiple_two_torsion_qq_not_half_translation
-- name    : Couret.InterIA.IntersectionTwo.Boundary.multiple_two_torsion_qq_not_half_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:33.396916+00:00
-- url     : https://prove2.me/theorems/e6cc884b-a396-4c7c-a7cc-95b5da92bb35
-- title:
--   A multiple-two-torsion configuration
-- statement:
--   In $G=(\mathbb Z/2\mathbb Z)^3$, let $S=\{(0,0,0),(0,1,0),(0,0,1),(1,1,1)\}$, $T=\{(1,0,0),(1,1,0),(0,0,1),(1,1,1)\}$, $C=\{(0,0,1),(1,1,1)\}$ and $h=(1,0,0)$. Then $|S\cap T|=2$, $C+h\ne C$, and $S+h\ne T$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/BoundaryTwo.lean, lines 43–49; source file SHA-256 4fe3c821c63fdd52714da014cbf6366a960267e0103927cffe51c8d7d1201467; theorem Couret.InterIA.IntersectionTwo.Boundary.multiple_two_torsion_qq_not_half_translation

import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
import Definitions.Def_Couret_IntersectionTwo_2d7b2419466c
import Definitions.Def_Couret_SingleSwap_148f04e2e72b
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
import Definitions.Def_Couret_IntersectionTwo_2d7b2419466c
import Definitions.Def_Couret_SingleSwap_148f04e2e72b
import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
import Definitions.Def_Couret_TranslationControls_1ed5eea33a54

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo.Boundary
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem multiple_two_torsion_qq_not_half_translation :
    (({(0,0,0),(0,1,0),(0,0,1),(1,1,1)} : Finset (ZMod 2 × ZMod 2 × ZMod 2)) ∩
      {(1,0,0),(1,1,0),(0,0,1),(1,1,1)}).card=2 ∧
    ({(0,0,1),(1,1,1)} : Finset (ZMod 2 × ZMod 2 × ZMod 2)).image
      (fun x => x+(1,0,0)) ≠ {(0,0,1),(1,1,1)} ∧
    ({(0,0,0),(0,1,0),(0,0,1),(1,1,1)} : Finset (ZMod 2 × ZMod 2 × ZMod 2)).image
      (fun x => x+(1,0,0)) ≠ {(1,0,0),(1,1,0),(0,0,1),(1,1,1)} := by sorry


end Couret.InterIA.IntersectionTwo.Boundary
