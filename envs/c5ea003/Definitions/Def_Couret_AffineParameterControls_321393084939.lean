-- Prove2me | Definitions.Def_Couret_AffineParameterControls_321393084939
-- name    : Couret_AffineParameterControls_321393084939
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:37.914381+00:00
-- url     : https://prove2.me/theorems/ae901dd2-e29b-40dd-962e-8743c78ab701
-- title:
--   Controlled quarter-pattern normal forms
-- statement:
--   For $S,T\subseteq\mathbb Z/(2m)$, the controlled form requires $2m=4q$ with $q>0$ even, a common affine automorphism $z\mapsto uz+v$ with $u$ a unit, and a parameter $x\notin\{0,q,2q,3q\}$ sending the supports to $$\{0,q,x,x+2q\},\qquad\{0,q,x+q,x+3q\}.$$ The predicate records all arithmetic and parameter exclusions needed for this normal form.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineParameterControls.lean; source file SHA-256 b23f6d173f81bdcce0efd0f521f478b044082f8c922fd091f81c4bf2ca25e413

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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]







def TwoControlledForm (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ q : ℕ, 0 < q ∧ 2*m=4*q ∧ Even q ∧ ∃ u : (ZMod (2*m))ˣ, ∃ v x : ZMod (2*m),
    x ∉ ({0,(q : ZMod (2*m)),2 • (q : ZMod (2*m)),3 • (q : ZMod (2*m))} : Finset (ZMod (2*m))) ∧
    S.image (fun z => (u : ZMod (2*m))*z+v)={0,(q : ZMod (2*m)),x,x+2 • (q : ZMod (2*m))} ∧
    T.image (fun z => (u : ZMod (2*m))*z+v)={0,(q : ZMod (2*m)),x+q,x+3 • (q : ZMod (2*m))}





end Couret.InterIA.Catalogue.Parameters


