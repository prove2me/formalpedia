-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
-- name    : Couret.STROBO2TORS.three_torsion_neg
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:16.635192+00:00
-- url     : https://prove2.me/theorems/a97e761d-aa43-4336-89fd-4e364ff03e38
-- title:
--   Negation preserves three-torsion
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For $v\in G$ with $3v=0$, $$3(-v)=0.$$
--
--   The zero element is included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 363–367; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.three_torsion_neg

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















section Finite

variable [Fintype G]

theorem three_torsion_neg (v : G) (hv : (v + v) + v = 0) :
    ((-v) + (-v)) + (-v) = 0 := by sorry








































end Finite
end Couret.STROBO2TORS
