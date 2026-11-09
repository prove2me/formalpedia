-- Prove2me | Theorems.Thm_Couret_InterIA_AbelianBoundary_double_equals_opposite_double
-- name    : Couret.InterIA.AbelianBoundary.double_equals_opposite_double
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:18.43188+00:00
-- url     : https://prove2.me/theorems/9d1bbb4c-6ea7-4323-89b3-4272cb69286a
-- title:
--   Opposite equal doubles force four-torsion
-- statement:
--   Let $H$ be an abelian group and $a,d\in H$ satisfy $d=-a$ and $2a=2d$. Then $$4a=0.$$
--
--   This extracts the four-torsion obstruction.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ReverseMatching.lean, lines 33–39; source file SHA-256 b77b158445897505c2a291e6886b5611971702cef47a8ab244375e44271880e4; theorem Couret.InterIA.AbelianBoundary.double_equals_opposite_double

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

theorem double_equals_opposite_double (a d : H)
    (hd : d = -a) (hh : a + a = d + d) :
    (a + a) + (a + a) = 0 := by sorry


end Couret.InterIA.AbelianBoundary
