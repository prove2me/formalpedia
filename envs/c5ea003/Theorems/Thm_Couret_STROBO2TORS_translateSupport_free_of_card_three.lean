-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
-- name    : Couret.STROBO2TORS.translateSupport_free_of_card_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:37.671697+00:00
-- url     : https://prove2.me/theorems/41d0e3d8-7f8c-4e9d-8c50-63127c519cd5
-- title:
--   Two-torsion acts freely on three-element supports
-- statement:
--   Let $G$ be an abelian group. Let $S\subseteq G$ have three elements and let $u\in G$ satisfy $2u=0$. If $S+u=S$, then
--
--   $$u=0.$$
--
--   This is the freeness needed for exact orbit counts.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 14–19; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.translateSupport_free_of_card_three

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_translation_free
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem translateSupport_free_of_card_three (S : Finset G)
    (hS : S.card = 3) (u : G) (hu : u + u = 0)
    (heq : translateSupport S u = S) : u = 0 := by sorry




















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
