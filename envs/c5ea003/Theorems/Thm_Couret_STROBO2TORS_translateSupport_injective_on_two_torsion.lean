-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective_on_two_torsion
-- name    : Couret.STROBO2TORS.translateSupport_injective_on_two_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:42.724667+00:00
-- url     : https://prove2.me/theorems/ceb53bf0-da57-46ee-b03e-cde367467a1a
-- title:
--   Two-torsion translates of a triple are distinct
-- statement:
--   In any abelian group, let $|S|=3$ and $2u=2v=0$. Then
--
--   $$S+u=S+v\Longrightarrow u=v.$$
--
--   This is freeness of the two-torsion action on odd-sized triple supports.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 21–35; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.translateSupport_injective_on_two_torsion

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem translateSupport_injective_on_two_torsion (S : Finset G)
    (hS : S.card = 3) (u v : G) (hu : u + u = 0) (hv : v + v = 0)
    (heq : translateSupport S u = translateSupport S v) : u = v := by sorry


















section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
