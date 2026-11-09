-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_inter_translateSupport_add_mem
-- name    : Couret.STROBO2TORS.inter_translateSupport_add_mem
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:03.123252+00:00
-- url     : https://prove2.me/theorems/8118b914-9bc5-4d94-9740-2806954d2372
-- title:
--   Intersection with a half-turn translate is stable
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For a finite support $S$, $u,x\in G$, with $2u=0$ and $x\in S\cap(S+u)$, $$x+u\in S\cap(S+u).$$
--
--   The identity translation is allowed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaOrdinary.lean, lines 18–32; source file SHA-256 2006ecb1ce5730617c2f132dbf2d494c09dc95a856c20cf5b66aefc549c8dc26; theorem Couret.STROBO2TORS.inter_translateSupport_add_mem

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Ordinary partners and the intersection of distinct three-element supports.

The intersection of a support with its translate by a two-torsion element
is stable under that translation. A nonzero translation therefore cannot
leave exactly one point in the intersection. For distinct three-element
supports, the intersection has cardinality zero or two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem inter_translateSupport_add_mem
    (S : Finset G) (u : G) (hu : u + u = 0) (x : G)
    (hx : x ∈ S ∩ translateSupport S u) :
    x + u ∈ S ∩ translateSupport S u := by sorry





end Couret.STROBO2TORS
