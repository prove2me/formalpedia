-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalOffsets_iff
-- name    : Couret.STROBO2TORS.mem_exceptionalOffsets_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:12.867758+00:00
-- url     : https://prove2.me/theorems/c6dbc0ee-32e0-44db-a13c-98101cea9a29
-- title:
--   Membership in exceptional offsets
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For $v,d\in G$ with $2d=0$, $$v\in\operatorname{Offsets}_{\mathrm{exc}}(d)\iff 2v\ne0\text{ and }3v\in\{0,d\}.$$
--
--   This retains the nonzero-double exclusion explicitly.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 513–541; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.mem_exceptionalOffsets_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_triple_condition_iff
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalOffsets
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/

theorem mem_exceptionalOffsets_iff (v d : G) (hd : d + d = 0) :
    v ∈ exceptionalOffsets d ↔
      (v + v ≠ 0 ∧ (((v + v) + v = 0) ∨ ((v + v) + v = d))) := by sorry






end Finite
end Couret.STROBO2TORS
