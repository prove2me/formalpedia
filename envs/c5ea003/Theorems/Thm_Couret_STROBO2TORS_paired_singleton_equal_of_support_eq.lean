-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paired_singleton_equal_of_support_eq
-- name    : Couret.STROBO2TORS.paired_singleton_equal_of_support_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:12.165185+00:00
-- url     : https://prove2.me/theorems/de3648d2-c516-441a-b9ab-b259b5a7b0f4
-- title:
--   The singleton entry is intrinsic to a paired support
-- statement:
--   Let $G$ be an abelian group. Let $a,b,d,t,c,e\in G$ with $d,e$ nonzero two-torsion, $2a\ne2b$, and $2t\ne2c$. If
--
--   $$\{a,b,b+d\}=\{t,c,c+e\},$$
--
--   then $a=t$. This identifies the singleton entry across two paired presentations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 37–54; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.paired_singleton_equal_of_support_eq

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem paired_singleton_equal_of_support_eq (a b d t c e : G)
    (hd : d + d = 0) (he : e + e = 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b) (htc : t + t ≠ c + c)
    (hs : ({a, b, b + d} : Finset G) = {t, c, c + e}) : a = t := by sorry






section Finite

variable [Fintype G]

























































































end Finite
end Couret.STROBO2TORS
