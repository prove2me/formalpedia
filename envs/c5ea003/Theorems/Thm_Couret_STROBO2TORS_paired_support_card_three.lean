-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
-- name    : Couret.STROBO2TORS.paired_support_card_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:56.773975+00:00
-- url     : https://prove2.me/theorems/7a0de3a5-aa13-4586-a129-3a61c46df537
-- title:
--   A nondegenerate paired support has three elements
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For $a,b,d\in G$ with $2d=0$, $d\ne0$, and $2a\ne2b$, $$|\{a,b,b+d\}|=3.$$
--
--   This ensures the formal three-entry support has no repetitions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 57–61; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.paired_support_card_three

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem paired_support_card_three (a b d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hab : a + a ≠ b + b) :
    ({a, b, b + d} : Finset G).card = 3 := by sorry












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
