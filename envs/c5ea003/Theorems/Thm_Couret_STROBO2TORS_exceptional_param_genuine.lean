-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
-- name    : Couret.STROBO2TORS.exceptional_param_genuine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:54.596143+00:00
-- url     : https://prove2.me/theorems/0d3b4d4d-e368-4063-8404-3403c55d08c1
-- title:
--   A nonzero three-torsion shift changes a doubled anchor
-- statement:
--   Let $G$ be any abelian group and let $a,v\in G$ with $3v=0$ and $v\ne0$. Then
--
--   $$2a\ne2(a+v).$$
--
--   No finiteness is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 19–25; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptional_param_genuine

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem exceptional_param_genuine (a v : G)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    a + a ≠ (a + v) + (a + v) := by sorry












section Finite

variable [Fintype G]

























































































end Finite
end Couret.STROBO2TORS
