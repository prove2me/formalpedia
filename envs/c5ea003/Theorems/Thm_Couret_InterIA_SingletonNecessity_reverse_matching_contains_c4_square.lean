-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_reverse_matching_contains_c4_square
-- name    : Couret.InterIA.SingletonNecessity.reverse_matching_contains_c4_square
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:00:35.107116+00:00
-- url     : https://prove2.me/theorems/659e25fc-3c13-4998-8a97-1bd6978559f7
-- title:
--   Reverse matching forces an order-four square subgroup
-- statement:
--   Let $G$ be an abelian group. Let $a,b,c,d,e,f\in G$ satisfy $a=e+f$, $a+b=f$, $a+c=e$, $b+c=d$, $2a=2d$, $2b=2e$, and $a\ne d$, $b\ne e$, $c\ne f$. Then
--
--   $$\exists\phi:(\mathbb Z/4\mathbb Z)^2\hookrightarrow G\text{ additive}.$$
--
--   This extracts the structural obstruction from reverse matching.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/C4SquareAlgebra.lean, lines 78–127; source file SHA-256 b1ddfe1104c004b9b50f0fd1a5930f7f7032d7121a8aa07043d9dda7d26b4f8c; theorem Couret.InterIA.SingletonNecessity.reverse_matching_contains_c4_square

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
import Theorems.Thm_Couret_InterIA_AbelianBoundary_double_equals_opposite_double
import Theorems.Thm_Couret_InterIA_SingletonNecessity_contains_c4_square_of_four_torsion
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

theorem reverse_matching_contains_c4_square (a b c d e f : G)
    (ha : a = e+f) (hab : a+b = f) (hac : a+c = e) (hbc : b+c = d)
    (hda : a+a = d+d) (hdb : b+b = e+e)
    (had : a ≠ d) (hbe : b ≠ e) (hcf : c ≠ f) :
    ∃ φ : G4 →+ G, Function.Injective φ := by sorry


end Couret.InterIA.SingletonNecessity
