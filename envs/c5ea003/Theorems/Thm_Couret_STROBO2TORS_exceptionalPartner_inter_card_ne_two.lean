-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_inter_card_ne_two
-- name    : Couret.STROBO2TORS.exceptionalPartner_inter_card_ne_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:19.82844+00:00
-- url     : https://prove2.me/theorems/fa0d5041-beee-4468-8de1-f4d10294e84f
-- title:
--   Exceptional partners cannot meet in two points
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For finite supports $S,T\subseteq G$ satisfying the defined exceptional-partner relation, $$|S\cap T|\ne2.$$ No separate cardinality assumptions are added beyond that relation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaExceptional.lean, lines 181–185; source file SHA-256 7ad0b7bd33eeaf0f097636d13479f3ebf69e9c24f631fbe9e3fe824233819af6; theorem Couret.STROBO2TORS.exceptionalPartner_inter_card_ne_two

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_normalized_inter
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Intersection sizes for the exceptional branch of the triple-square
classification. The parameters below use the same coordinates as
ExceptionalPartner: the reflected doublet is based at b + b - a.
No finiteness assumption on the ambient abelian group is needed.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem exceptionalPartner_inter_card_ne_two (S T : Finset G)
    (he : ExceptionalPartner S T) : (S ∩ T).card ≠ 2 := by sorry



end Couret.STROBO2TORS
