-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
-- name    : Couret.STROBO2TORS.paramSupport_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:10.326946+00:00
-- url     : https://prove2.me/theorems/ad8d7cc3-d6d0-4db9-9890-7b4cf6e87ecb
-- title:
--   An exceptional parameter gives a triple
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For $a,d,v\in G$ with $2d=0$, $d\ne0$, $3v=0$, $v\ne0$, the parameter support satisfies $$|P(a,d,v)|=3.$$
--
--   This is the cardinality required for the exceptional parameterization. Here $P(a,d,v)=\{a,a+v,a+v+d\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 30–35; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.paramSupport_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem paramSupport_card (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (paramSupport ((a, d), v)).card = 3 := by sorry








section Finite

variable [Fintype G]

























































































end Finite
end Couret.STROBO2TORS
