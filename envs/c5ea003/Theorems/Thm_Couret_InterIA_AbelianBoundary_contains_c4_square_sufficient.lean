-- Prove2me | Theorems.Thm_Couret_InterIA_AbelianBoundary_contains_c4_square_sufficient
-- name    : Couret.InterIA.AbelianBoundary.contains_c4_square_sufficient
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:22.492757+00:00
-- url     : https://prove2.me/theorems/46edfc06-63e7-45fc-8bb0-479132a40357
-- title:
--   An embedded square of the cyclic group of order four gives a singleton collision
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $H$ be an abelian group admitting an injective additive map from $(\mathbb Z/4\mathbb Z)^2$. Then
--
--   $$\exists A,B\subseteq H:\ |A|=|B|=4,\ |A\cap B|=1,\ R_A=R_B.$$
--
--   This provides the sufficient direction of the singleton-intersection collision criterion.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-boundary-20261103/EmbeddingTransport.lean, lines 37–45; source file SHA-256 10f68a5cfe5d6bb349f7f53be056fc22180a32943905fcd0344029778c6c8eca; theorem Couret.InterIA.AbelianBoundary.contains_c4_square_sufficient

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
import Theorems.Thm_Couret_InterIA_AbelianBoundary_common_singleton
import Theorems.Thm_Couret_InterIA_AbelianBoundary_source_card
import Theorems.Thm_Couret_InterIA_AbelianBoundary_square_collision
import Theorems.Thm_Couret_InterIA_AbelianBoundary_target_card
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.AbelianBoundary
open Finset Couret.InterIA.Parity
variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H]

theorem contains_c4_square_sufficient (f : G4 →+ H) (hf : Function.Injective f) :
    ∃ A B : Finset H, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      (∀ z, orderedSquare A z=orderedSquare B z) := by sorry

end Couret.InterIA.AbelianBoundary
