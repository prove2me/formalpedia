-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_eq_twice
-- name    : Couret.STROBO2TORS.orderedNontranslationPairs_card_eq_twice
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:06.023035+00:00
-- url     : https://prove2.me/theorems/4a3a0cf1-74b0-4409-b8d0-37bb717804d2
-- title:
--   Two orientations per zero-free nontranslation pair
-- statement:
--   In any finite additive commutative group G with decidable equality, the number of ordered pairs (S,T) of zero-free three-element supports having the same labelled ordered additive convolution square and with T unequal to every translate of S is twice the number of their unordered two-element support sets {S,T}. Both counts are finite-set cardinalities in ℕ, and the empty case is included. The translation exclusion concerns all group translations, not only two-torsion translations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 398–409; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.orderedNontranslationPairs_card_eq_twice

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nontranslationPairs_preimage
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]
































attribute [local instance] Classical.propDecidable

theorem orderedNontranslationPairs_card_eq_twice :
    (orderedNontranslationPairs : Finset (Finset G × Finset G)).card =
      2 * (nontranslationPairs : Finset (Finset (Finset G))).card := by sorry












end Finite
end Couret.STROBO2TORS
