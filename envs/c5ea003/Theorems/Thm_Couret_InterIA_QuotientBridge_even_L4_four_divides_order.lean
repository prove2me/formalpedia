-- Prove2me | Theorems.Thm_Couret_InterIA_QuotientBridge_even_L4_four_divides_order
-- name    : Couret.InterIA.QuotientBridge.even_L4_four_divides_order
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:27.473539+00:00
-- url     : https://prove2.me/theorems/c09abfc8-d3c5-4b33-b5e3-d81e81a15c2c
-- title:
--   Divisibility from a nonaffine collision
-- statement:
--   For every positive natural $m$ and four-element subsets $S,T\subseteq\mathbb Z/(2m)\mathbb Z$ with equal ordered-pair sum counts at every residue, if no unit $u$ and residue $v$ satisfy $uS+v=T$, then $4$ divides $2m$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EvenL4Quotient.lean, lines 27–42; source file SHA-256 555bae2fa9f7cad3719e65789ea42150b7aade93421233a3a835cdc1a503a5f0; theorem Couret.InterIA.QuotientBridge.even_L4_four_divides_order

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Theorems.Thm_Couret_InterIA_QuotientBridge_normal_quotient_period
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.Projection
open Couret.InterIA.NormalForm

theorem even_L4_four_divides_order (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 4 ∣ 2*m := by sorry






end Couret.InterIA.QuotientBridge
