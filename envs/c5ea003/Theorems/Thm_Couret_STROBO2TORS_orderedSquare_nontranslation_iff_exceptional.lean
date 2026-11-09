-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedSquare_nontranslation_iff_exceptional
-- name    : Couret.STROBO2TORS.orderedSquare_nontranslation_iff_exceptional
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:39.536195+00:00
-- url     : https://prove2.me/theorems/c9515205-81c4-4d14-9271-a72a109f5692
-- title:
--   The nontranslation collision branch is exactly exceptional
-- statement:
--   Let $G$ be any abelian group and $S,T$ supports of size three. Write $R_S$ for their ordered pair-sum counts. Then
--
--   $$[R_S=R_T\land\nexists u,\ T=S+u]\iff\operatorname{ExceptionalPartner}(S,T).$$
--
--   Here exceptional means $S=\{a,b,b+d\}$, $T=\{a,2b-a,2b-a+d\}+u$ for $d\ne0$, $2d=2u=0$, $2a\ne2b$, $3(b-a)\in\{0,d\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationBridge.lean, lines 9–22; source file SHA-256 69eddf5a9bf0e6dd7b706b3e6d593c7d3d8cf875b213644de00a9d2d32bd5389; theorem Couret.STROBO2TORS.orderedSquare_nontranslation_iff_exceptional

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem orderedSquare_nontranslation_iff_exceptional
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z : G, orderedSquare S z = orderedSquare T z) ∧
      ¬ ∃ v : G, T = translateSupport S v) ↔ ExceptionalPartner S T := by sorry




end Couret.STROBO2TORS
