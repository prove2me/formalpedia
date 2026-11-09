-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_third_probe_separates_exceptional
-- name    : Couret.STROBO2TORS.recoh_third_probe_separates_exceptional
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:38.371588+00:00
-- url     : https://prove2.me/theorems/7a53a8a8-9bff-46ed-9c98-88d0fb30afaa
-- title:
--   A ternary character separates an exceptional pair
-- statement:
--   Let $G$ be an abelian group. Let $a,d,v,u\in G$ satisfy $2d=0$, $d\ne0$, $3v=0$, $v\ne0$. Let $\chi$ be a complex character with $\chi(d)=\chi(u)=1$ and $\chi(v)\ne1$. Set $S=\{a,a+v,a+v+d\}$ and $T=\{a,a-v,a-v+d\}+u$. Then
--
--   $$P_\chi(S)\ne P_\chi(T).$$
--
--   The shift $u$ itself need not be two-torsion; only its character value is prescribed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohReconstruction.lean, lines 109–146; source file SHA-256 513a4060ff87ff1fa62542ec6ee81bb251e2eebfa05d359dd9f60f5fb115b612; theorem Couret.STROBO2TORS.recoh_third_probe_separates_exceptional

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: reconstructing a cardinality-three support from its labelled ordered
square and a fixed bank of individual complex character coefficients.

The observation and the support cardinality are explicit. The classification
used below is the existing STROBO theorem, not an additional hypothesis.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_third_probe_separates_exceptional
    (chi : AddChar G ℂ) (a d v u : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hcd : chi d = 1) (hcu : chi u = 1) (hcv : chi v ≠ 1) :
    recohSupportProbe chi (paramSupport ((a, d), v)) ≠
      recohSupportProbe chi (translateSupport (paramSupport ((a, d), -v)) u) := by sorry








end Couret.STROBO2TORS
