-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paramSupport_parameters_unique
-- name    : Couret.STROBO2TORS.paramSupport_parameters_unique
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:57.282206+00:00
-- url     : https://prove2.me/theorems/b1b4f770-80b7-40bc-8914-fae2a7a4e47f
-- title:
--   Uniqueness of the canonical exceptional parameters
-- statement:
--   Let $G$ be an abelian group and $P(a,d,v)=\{a,a+v,a+v+d\}$. Assume $d,e$ are nonzero and killed by two, and $v,w$ are nonzero and killed by three. Then
--
--   $$P(a,d,v)=P(t,e,w)\Longrightarrow a=t,\quad d=e,\quad v=w.$$
--
--   No finiteness is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 56–89; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.paramSupport_parameters_unique

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_paired_singleton_equal_of_support_eq
import Theorems.Thm_Couret_STROBO2TORS_triple_sum_translate
import Theorems.Thm_Couret_STROBO2TORS_two_point_pair_direction
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem paramSupport_parameters_unique (a d v t e w : G)
    (hd : d + d = 0) (he : e + e = 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hv : (v + v) + v = 0) (hw : (w + w) + w = 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hs : paramSupport ((a, d), v) = paramSupport ((t, e), w)) :
    a = t ∧ d = e ∧ v = w := by sorry




section Finite

variable [Fintype G]

























































































end Finite
end Couret.STROBO2TORS
