-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_contains_c4_square_of_four_torsion
-- name    : Couret.InterIA.SingletonNecessity.contains_c4_square_of_four_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:59.298522+00:00
-- url     : https://prove2.me/theorems/c80267e9-f780-4b33-a05e-00307f10b44d
-- title:
--   Independent doubled four-torsion elements embed a square
-- statement:
--   Let $G$ be an abelian group. Let $a,b\in G$ satisfy $4a=4b=0$, $2a\ne0$, $2b\ne0$, and $2a\ne2b$. Then
--
--   $$\exists f:(\mathbb Z/4\mathbb Z)^2\hookrightarrow G\text{ additive}.$$
--
--   This detects a copy of the order-four square from its two doubled generators.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/C4SquareAlgebra.lean, lines 62–76; source file SHA-256 b1ddfe1104c004b9b50f0fd1a5930f7f7032d7121a8aa07043d9dda7d26b4f8c; theorem Couret.InterIA.SingletonNecessity.contains_c4_square_of_four_torsion

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_injective_of_double_images
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

theorem contains_c4_square_of_four_torsion (a b : G)
    (ha : (4:ℤ) • a = 0) (hb : (4:ℤ) • b = 0)
    (ha2 : a+a ≠ 0) (hb2 : b+b ≠ 0) (hab2 : a+a ≠ b+b) :
    ∃ f : G4 →+ G, Function.Injective f := by sorry




end Couret.InterIA.SingletonNecessity
