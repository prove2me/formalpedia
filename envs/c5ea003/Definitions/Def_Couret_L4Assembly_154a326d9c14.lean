-- Prove2me | Definitions.Def_Couret_L4Assembly_154a326d9c14
-- name    : Couret_L4Assembly_154a326d9c14
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:05.952965+00:00
-- url     : https://prove2.me/theorems/26c498c1-c228-46fb-a724-26fcce0a9af5
-- title:
--   Affine equivalence of cyclic supports
-- statement:
--   For supports $S,T\subseteq\mathbb Z/n$, affine equivalence means $$T=\{ux+v:x\in S\}$$ for some unit $u\in(\mathbb Z/n)^\times$ and translation $v$. This is the equivalence relation used to distinguish genuinely different collision supports from changes of affine coordinates.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/L4Assembly.lean; source file SHA-256 963e8dd3e3584e7170596d25b739b90c527798bb137acf05581e70913cf1549c

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

/-- The usual affine action: one unit multiplier and one common offset. -/
def AffineEquivalent {n : ℕ} (S T : Finset (ZMod n)) : Prop :=
  ∃ u : (ZMod n)ˣ, ∃ v : ZMod n, S.image (fun x => (u : ZMod n)*x+v)=T









end Couret.InterIA.NormalForm


