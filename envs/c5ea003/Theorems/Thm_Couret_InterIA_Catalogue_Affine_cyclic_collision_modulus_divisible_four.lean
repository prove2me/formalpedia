-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_cyclic_collision_modulus_divisible_four
-- name    : Couret.InterIA.Catalogue.Affine.cyclic_collision_modulus_divisible_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:38.880721+00:00
-- url     : https://prove2.me/theorems/014081f3-abef-4100-9452-f73d14cf1617
-- title:
--   cyclic collision modulus divisible four
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every natural number n≥4 and finite S,T⊆ℤ/nℤ, if |S|=|T|=4, Q(S,z)=Q(T,z) for every z∈ℤ/nℤ, and S,T are not affinely equivalent, then 4 divides n.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineFormAssembly.lean, lines 29–38; source file SHA-256 950577d51e759236cc4f563502c0e426bd57982b418ff30d743f6f7c8b79152e; theorem Couret.InterIA.Catalogue.Affine.cyclic_collision_modulus_divisible_four

import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_collision_affine_forms
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Definitions.Def_Couret_AffineSupportForms_4a272694daca

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts Couret.InterIA.Parity

theorem cyclic_collision_modulus_divisible_four (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) : 4 ∣ n := by sorry


end Couret.InterIA.Catalogue.Affine
