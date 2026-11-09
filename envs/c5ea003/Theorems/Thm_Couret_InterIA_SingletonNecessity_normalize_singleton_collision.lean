-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_normalize_singleton_collision
-- name    : Couret.InterIA.SingletonNecessity.normalize_singleton_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:27.713213+00:00
-- url     : https://prove2.me/theorems/6c07288f-0177-4bcf-b765-82d4613d3fa0
-- title:
--   Normalize a singleton-intersection collision
-- statement:
--   Let $G$ be an abelian group and $A,B\subseteq G$ each have four elements, intersect in exactly one element, and satisfy $Q_A=Q_B$. There exist four-element supports $A_0,B_0$ with $$A_0\cap B_0=\{0\},\qquad Q_{A_0}=Q_{B_0}.$$
--
--   This places the shared point at the identity.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SingletonNormalization.lean, lines 40–48; source file SHA-256 b79e3a7dcd27241fd2b42296a8a3585acdf1ea087086ba375ded443d56f96cf2; theorem Couret.InterIA.SingletonNecessity.normalize_singleton_collision

import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
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

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem normalize_singleton_collision (A B : Finset G)
    (ha : A.card=4) (hb : B.card=4) (hi : (A ∩ B).card=1)
    (hc : ∀ z, orderedSquare A z=orderedSquare B z) :
    ∃ A₀ B₀ : Finset G, A₀.card=4 ∧ B₀.card=4 ∧ A₀ ∩ B₀={0} ∧
      (∀ z, orderedSquare A₀ z=orderedSquare B₀ z) := by sorry


end Couret.InterIA.SingletonNecessity
