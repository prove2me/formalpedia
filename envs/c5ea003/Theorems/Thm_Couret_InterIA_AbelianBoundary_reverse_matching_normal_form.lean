-- Prove2me | Theorems.Thm_Couret_InterIA_AbelianBoundary_reverse_matching_normal_form
-- name    : Couret.InterIA.AbelianBoundary.reverse_matching_normal_form
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:26.244604+00:00
-- url     : https://prove2.me/theorems/d922b74a-16ef-444d-adbd-e4ac140e31b9
-- title:
--   Normal form of reverse matching
-- statement:
--   Let $a,b,c,d,e,f$ belong to an abelian group, with $a=e+f$, $a+b=f$, $a+c=e$, and $b+c=d$. Then
--
--   $$a+b+c=0,\qquad d=-a,\qquad e=-b,\qquad f=-c.$$
--
--   This expresses the matching equations in a symmetric normal form.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ReverseMatching.lean, lines 11–31; source file SHA-256 b77b158445897505c2a291e6886b5611971702cef47a8ab244375e44271880e4; theorem Couret.InterIA.AbelianBoundary.reverse_matching_normal_form

import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

/- Algebraic consequences of the surviving matching.
Compiled locally; the full parity-to-matching reduction is separate. -/
set_option autoImplicit false

namespace Couret.InterIA.AbelianBoundary

variable {H : Type*} [AddCommGroup H]

theorem reverse_matching_normal_form
    (a b c d e f : H)
    (ha : a = e + f)
    (hab : a + b = f) (hac : a + c = e) (hbc : b + c = d) :
    a + b + c = 0 ∧ d = -a ∧ e = -b ∧ f = -c := by sorry




end Couret.InterIA.AbelianBoundary
