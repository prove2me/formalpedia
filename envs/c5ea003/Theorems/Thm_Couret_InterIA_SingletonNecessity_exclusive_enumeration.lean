-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_exclusive_enumeration
-- name    : Couret.InterIA.SingletonNecessity.exclusive_enumeration
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:08.527724+00:00
-- url     : https://prove2.me/theorems/b13d2e50-5f76-4153-b047-4c0016be3fe1
-- title:
--   Enumerating two four-sets with one common zero
-- statement:
--   Let $G$ be an abelian group. Let $A,B\subseteq G$ have four elements each and satisfy $A\cap B=\{0\}$. There exist six nonzero pairwise distinct elements $x_0,\ldots,x_5$ such that
--
--   $$A=\{0,x_0,x_1,x_2\},\qquad B=\{0,x_3,x_4,x_5\}.$$
--
--   This supplies labels for the singleton-intersection matching argument.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ExclusiveEnumeration.lean, lines 10–59; source file SHA-256 e9335ae75c793b443dea30485ce117fdc77557ebd960ab9a5308276ea8778067; theorem Couret.InterIA.SingletonNecessity.exclusive_enumeration

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_distinctLabels_of_injective_nonzero
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem exclusive_enumeration (A B : Finset G) (ha : A.card=4) (hb : B.card=4)
    (hi : A ∩ B={0}) :
    ∃ x : Fin 6 → G, SevenDistinct x ∧ supportLeft x=A ∧ supportRight x=B := by sorry


end Couret.InterIA.SingletonNecessity
