-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_injective_of_double_images
-- name    : Couret.InterIA.SingletonNecessity.injective_of_double_images
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:49.679517+00:00
-- url     : https://prove2.me/theorems/4bbf2369-589f-442f-ba5f-5e87b0af2367
-- title:
--   Injectivity from the three nonzero doubled images
-- statement:
--   Let $G$ be an abelian group. Let $f:(\mathbb Z/4\mathbb Z)^2\to G$ be additive. Suppose $f(2,0)$ and $f(0,2)$ are nonzero and different. Then
--
--   $$f\text{ is injective}.$$
--
--   The criterion checks only the nontrivial two-torsion of the domain.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/C4SquareAlgebra.lean, lines 29–60; source file SHA-256 b1ddfe1104c004b9b50f0fd1a5930f7f7032d7121a8aa07043d9dda7d26b4f8c; theorem Couret.InterIA.SingletonNecessity.injective_of_double_images

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
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

theorem injective_of_double_images (f : G4 →+ G)
    (ha : f (2,0) ≠ 0) (hb : f (0,2) ≠ 0)
    (hab : f (2,0) ≠ f (0,2)) : Function.Injective f := by sorry






end Couret.InterIA.SingletonNecessity
