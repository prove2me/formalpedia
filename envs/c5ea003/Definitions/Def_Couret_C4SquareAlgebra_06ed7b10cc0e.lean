-- Prove2me | Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
-- name    : Couret_C4SquareAlgebra_06ed7b10cc0e
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:33.582933+00:00
-- url     : https://prove2.me/theorems/4fa9e185-8c34-4a44-90fb-3cf6d6f4de63
-- title:
--   Additive maps from the cyclic group of order four
-- statement:
--   For an element $a$ of an abelian group satisfying $4a=0$, defines the additive map $\mathbb Z/4\mathbb Z\to G$ induced by $n\mapsto na$. This is the basic coordinate map used to construct embeddings of the square of the order-four cyclic group.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/C4SquareAlgebra.lean; source file SHA-256 b1ddfe1104c004b9b50f0fd1a5930f7f7032d7121a8aa07043d9dda7d26b4f8c

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
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

def fourthMap (a : G) (ha : (4:ℤ) • a = 0) : ZMod 4 →+ G :=
  ZMod.lift 4 ⟨{
    toFun := fun n => n • a
    map_zero' := by simp
    map_add' := by intro m n; exact add_zsmul a m n
  }, ha⟩













end Couret.InterIA.SingletonNecessity


