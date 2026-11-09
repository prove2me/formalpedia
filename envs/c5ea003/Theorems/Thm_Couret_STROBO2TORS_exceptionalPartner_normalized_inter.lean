-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_normalized_inter
-- name    : Couret.STROBO2TORS.exceptionalPartner_normalized_inter
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:53:51.883024+00:00
-- url     : https://prove2.me/theorems/e44ae999-44f3-43f5-974c-7fc55c547753
-- title:
--   Intersection of a normalized exceptional pair
-- statement:
--   Let $G$ be an abelian group. Let $a,b,d,u\in G$ with $2d=2u=0$, $2a\ne2b$, and $3(b-a)\in\{0,d\}$. Set $S=\{a,b,b+d\}$ and $R=\{a,2b-a,2b-a+d\}$. Then
--
--   $$S\cap(R+u)=\begin{cases}\{a\},&u=0,\\\varnothing,&u\ne0.\end{cases}$$
--
--   This specifies the exact overlap in the reflected branch.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaExceptional.lean, lines 109–149; source file SHA-256 7ad0b7bd33eeaf0f097636d13479f3ebf69e9c24f631fbe9e3fe824233819af6; theorem Couret.STROBO2TORS.exceptionalPartner_normalized_inter

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Intersection sizes for the exceptional branch of the triple-square
classification. The parameters below use the same coordinates as
ExceptionalPartner: the reflected doublet is based at b + b - a.
No finiteness assumption on the ambient abelian group is needed.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem exceptionalPartner_normalized_inter
    (a b d u : G) (hd : d + d = 0) (hab : a + a ≠ b + b)
    (hu : u + u = 0)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    ({a, b, b + d} : Finset G) ∩
        translateSupport ({a, b + b - a, (b + b - a) + d} : Finset G) u =
      if u = 0 then {a} else ∅ := by sorry











end Couret.STROBO2TORS
