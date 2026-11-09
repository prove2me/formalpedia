-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryPartner_inter_card_eq_zero_or_two
-- name    : Couret.STROBO2TORS.ordinaryPartner_inter_card_eq_zero_or_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:54:54.207034+00:00
-- url     : https://prove2.me/theorems/13978be6-9f75-417d-961a-e7e169661e2e
-- title:
--   Ordinary partners meet in zero or two points
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For distinct three-element supports $S,T$ with $O(S,T)$, $$|S\cap T|=0\quad\text{or}\quad|S\cap T|=2.$$
--
--   This excludes one-point intersections for ordinary partners. The ordinary relation $O(S,T)$ means $T=S+u$ for some $u$ with $2u=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaOrdinary.lean, lines 34–68; source file SHA-256 2006ecb1ce5730617c2f132dbf2d494c09dc95a856c20cf5b66aefc549c8dc26; theorem Couret.STROBO2TORS.ordinaryPartner_inter_card_eq_zero_or_two

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_inter_translateSupport_add_mem
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Ordinary partners and the intersection of distinct three-element supports.

The intersection of a support with its translate by a two-torsion element
is stable under that translation. A nonzero translation therefore cannot
leave exactly one point in the intersection. For distinct three-element
supports, the intersection has cardinality zero or two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem ordinaryPartner_inter_card_eq_zero_or_two
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3)
    (hST : S ≠ T) (hOrd : OrdinaryPartner S T) :
    (S ∩ T).card = 0 ∨ (S ∩ T).card = 2 := by sorry



end Couret.STROBO2TORS
