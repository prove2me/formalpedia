-- Prove2me | Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
-- name    : Couret_Strobo2TorsPairCount_5c76f0dc12bb
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:14.717001+00:00
-- url     : https://prove2.me/theorems/48d65481-91e7-4659-94a8-6e4766ae3d64
-- title:
--   Zero-free nontranslation pairs and their parameters
-- statement:
--   Defines a nontranslation collision as two zero-free three-element supports with identical ordered squares and no translation between them. For finite groups, parametrizes such pairs by a nonzero two-torsion element, a nonzero three-torsion element, an anchor, and an admissible two-torsion translate. Defines ordered pairs and their unordered two-support images.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd

import Aesop
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





/-- The actual observable and nontranslation by ANY element of G. -/
def NontranslationCollision (S T : Finset G) : Prop :=
  S.card = 3 ∧ T.card = 3 ∧ 0 ∉ S ∧ 0 ∉ T ∧
    (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
    ¬ ∃ u : G, T = translateSupport S u

section Finite
variable [Fintype G]







/-- Admissible singleton/translation choices for fixed nonzero d and v. -/
def pairLifts (d v : G) : Finset (G × G) :=
  ((Finset.univ : Finset G) ×ˢ (twoTorsion : Finset G)).filter
    (fun p => 0 ∉ paramSupport ((p.1,d),v) ∧
      0 ∉ translateSupport (paramSupport ((p.1,d),-v)) p.2)












abbrev PairParameter (G : Type*) := Σ _ : G × G, G × G

def pairParameters : Finset (PairParameter G) :=
  (((twoTorsion : Finset G).erase 0) ×ˢ ((threeTorsion : Finset G).erase 0)).sigma
    (fun dv => pairLifts dv.1 dv.2)

def pairRealization (p : PairParameter G) : Finset G × Finset G :=
  (paramSupport ((p.2.1,p.1.1),p.1.2),
    translateSupport (paramSupport ((p.2.1,p.1.1),-p.1.2)) p.2.2)







attribute [local instance] Classical.propDecidable

noncomputable def orderedNontranslationPairs : Finset (Finset G × Finset G) :=
  ((tripleSupports : Finset (Finset G)) ×ˢ tripleSupports).filter
    (fun p => NontranslationCollision p.1 p.2)







/-- A pair is a two-element Finset of supports: orientation is forgotten once. -/
noncomputable def nontranslationPairs : Finset (Finset (Finset G)) :=
  (orderedNontranslationPairs : Finset (Finset G × Finset G)).image (fun p => {p.1,p.2})



















end Finite
end Couret.STROBO2TORS


