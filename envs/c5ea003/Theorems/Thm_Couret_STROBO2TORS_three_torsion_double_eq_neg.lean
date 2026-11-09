-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
-- name    : Couret.STROBO2TORS.three_torsion_double_eq_neg
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:20.207178+00:00
-- url     : https://prove2.me/theorems/75118283-bc5c-43e6-ac9a-a2b233cfb630
-- title:
--   Doubling a three-torsion element negates it
-- statement:
--   In any abelian group, for $v$ with $3v=0$,
--
--   $$2v=-v.$$
--
--   The case $v=0$ is included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 12–13; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.three_torsion_double_eq_neg

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem three_torsion_double_eq_neg (v : G) (hv : (v + v) + v = 0) :
    v + v = -v := by sorry


section Finite

variable [Fintype G]















































































end Finite
end Couret.STROBO2TORS
