-- Prove2me | Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
-- name    : Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:59.19763+00:00
-- url     : https://prove2.me/theorems/a395dcba-48c4-419c-8b7a-601f885610cd
-- title:
--   Bridge between translation and partner classifications
-- statement:
--   Provides the proved equivalence, for two three-element supports, between equal ordered squares together with existence of any translation and the ordinary-partner relation. The latter specifically uses a two-torsion translation. This helper distinguishes the ordinary branch from genuinely nontranslation exceptional collisions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationBridge.lean; source file SHA-256 69eddf5a9bf0e6dd7b706b3e6d593c7d3d8cf875b213644de00a9d2d32bd5389

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



/-- Any translated ordered-square collision of triples is an ordinary 2-torsion partner. -/
theorem orderedSquare_translation_iff_ordinary
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z : G, orderedSquare S z = orderedSquare T z) ∧
      ∃ v : G, T = translateSupport S v) ↔ OrdinaryPartner S T := by
  constructor
  · rintro ⟨hEq, ⟨v, hv⟩⟩
    rcases (orderedSquare_classification_iff S T hS hT).mp hEq with hOrd | hExc
    · exact hOrd
    · exact False.elim
        ((exceptionalPartner_not_any_translation S T hS hT hExc) ⟨v, hv⟩)
  · rintro ⟨u, hu, hTrans⟩
    exact ⟨(orderedSquare_classification_iff S T hS hT).mpr
      (Or.inl ⟨u, hu, hTrans⟩), ⟨u, hTrans⟩⟩

end Couret.STROBO2TORS


