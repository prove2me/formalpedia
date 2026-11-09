-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_NontranslationCollision_ne
-- name    : Couret.STROBO2TORS.NontranslationCollision.ne
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:07.666591+00:00
-- url     : https://prove2.me/theorems/e05d0198-471b-40b1-896a-751793b0bab9
-- title:
--   A nontranslation collision has distinct supports
-- statement:
--   Let G be an abelian additive group with decidable equality, and let S,T be finite subsets of G. Assume NontranslationCollision S T: both supports have cardinality three, neither contains zero, their labelled ordered-square functions agree at every z in G, and there is no u in G such that T = {x+u : x in S}. The ordered-square value counts all ordered pairs (x,y) in the support with x+y=z, including diagonal pairs. Then S ≠ T. The ambient group need not be finite.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 358–362; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.NontranslationCollision.ne

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

omit [Fintype G] in
theorem NontranslationCollision.ne {S T : Finset G} (h : NontranslationCollision S T) : S ≠ T := by sorry


















end Finite
end Couret.STROBO2TORS
