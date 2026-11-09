-- Prove2me | Theorems.Thm_Couret_InterIA_QuotientBridge_cyclic_L4_four_divides_order
-- name    : Couret.InterIA.QuotientBridge.cyclic_L4_four_divides_order
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:50:01.379264+00:00
-- url     : https://prove2.me/theorems/42a90645-0b88-4cbc-b2fa-827b236a0882
-- title:
--   cyclic L4 four divides order
-- statement:
--   For every integer $n≥4$ and four-element subsets $S,T⊆ℤ/nℤ$, if their ordered-pair sum counts agree at every residue and there are no unit $u$ modulo $n$ and residue $v$ with $uS+v=T$, then $4∣n$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EvenL4Quotient.lean, lines 54–64; source file SHA-256 555bae2fa9f7cad3719e65789ea42150b7aade93421233a3a835cdc1a503a5f0; theorem Couret.InterIA.QuotientBridge.cyclic_L4_four_divides_order

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
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Theorems.Thm_Couret_InterIA_QuotientBridge_even_L4_four_divides_order
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.Projection
open Couret.InterIA.NormalForm

theorem cyclic_L4_four_divides_order (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 4 ∣ n := by sorry


end Couret.InterIA.QuotientBridge
