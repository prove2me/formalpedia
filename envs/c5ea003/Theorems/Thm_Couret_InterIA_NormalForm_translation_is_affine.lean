-- Prove2me | Theorems.Thm_Couret_InterIA_NormalForm_translation_is_affine
-- name    : Couret.InterIA.NormalForm.translation_is_affine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:55.478492+00:00
-- url     : https://prove2.me/theorems/68f1d1ce-66cc-4be7-aa25-5519a6ce5f56
-- title:
--   Translations are affine
-- statement:
--   For every natural $n$, finite subsets $S,T\subseteq R=\operatorname{ZMod}(n)$ and $v\in R$, if $S+v=T$, then there exist a unit $u\in R^\times$ and $w\in R$ with $uS+w=T$. This includes empty sets and $n=0$, where $R=\mathbb Z$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/L4Assembly.lean, lines 11–14; source file SHA-256 963e8dd3e3584e7170596d25b739b90c527798bb137acf05581e70913cf1549c; theorem Couret.InterIA.NormalForm.translation_is_affine

import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem translation_is_affine {n : ℕ} (S T : Finset (ZMod n)) (v : ZMod n)
    (ht : S.image (fun x => x+v)=T) : AffineEquivalent S T := by sorry








end Couret.InterIA.NormalForm
