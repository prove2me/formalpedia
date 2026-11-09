-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_parity_has_pairing
-- name    : Couret.InterIA.SingletonNecessity.parity_has_pairing
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:32.93408+00:00
-- url     : https://prove2.me/theorems/4b42d0bd-dbe7-4662-8a2e-b5decc35c611
-- title:
--   Parity equality gives a pairing of six values
-- statement:
--   Let $d_0,\ldots,d_5$ be elements of a type with decidable equality. Suppose that for every value $z$, its number of occurrences among $d_0,d_1,d_2$ has the same parity as among $d_3,d_4,d_5$. Then
--
--   $$\{0,1,2,3,4,5\}\text{ can be partitioned into three pairs }\{i,j\}\text{ with }d_i=d_j.$$
--
--   The pairing may join indices on either side. This turns pointwise parity data into a finite matching.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SixDoublePairing.lean, lines 26–1009; source file SHA-256 e79e5620a66aef560a893ef2c2f1adb2de1fc3f858804fed5dd6dbd8a3babec4; theorem Couret.InterIA.SingletonNecessity.parity_has_pairing

import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
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
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.SingletonNecessity

theorem parity_has_pairing {α : Type*} [DecidableEq α] (d : Fin 6 → α)
    (hp : FibreParity d) : HasPairing d := by sorry

end Couret.InterIA.SingletonNecessity
