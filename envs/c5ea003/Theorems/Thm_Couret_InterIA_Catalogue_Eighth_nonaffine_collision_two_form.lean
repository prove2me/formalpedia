-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Eighth_nonaffine_collision_two_form
-- name    : Couret.InterIA.Catalogue.Eighth.nonaffine_collision_two_form
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:40.989931+00:00
-- url     : https://prove2.me/theorems/bed42a77-c85d-44f2-89e8-b7d02e569fdc
-- title:
--   nonaffine collision two form
-- statement:
--   For every positive integer $m$ and finite subsets $S,T$ of $R=ℤ/(2m)ℤ$, assume $|S|=|T|=4$, that for every $z∈R$ the numbers of ordered pairs in $S²$ and $T²$ summing to $z$ agree, and that there are no unit $u∈R$ and $v∈R$ with $uS+v=T$. There exists $t∈\{0,m\}$ such that, writing $T_t=T+t$, there exist a positive even integer $q$ with $2m=4q$, a unit $u∈R$, and $v,x∈R$, with $x∉\{0,q,2q,3q\}$, such that $uS+v=\{0,q,x,x+2q\}$ and $uT_t+v=\{0,q,x+q,x+3q\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EighthBoundary.lean, lines 24–34; source file SHA-256 f9aba8033eef5d5adcace2af831ad4ebd4ea101c00db1ec77bf9732d46da9b47; theorem Couret.InterIA.Catalogue.Eighth.nonaffine_collision_two_form

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_reflection_affine
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_collision_controlled_affine_forms
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Affine
open Couret.InterIA.Catalogue.AffineTransport Couret.InterIA.Catalogue.Parameters
open Couret.InterIA.Parity

theorem nonaffine_collision_two_form (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧ TwoControlledForm m S (T.image (fun x => x+t)) := by sorry


end Couret.InterIA.Catalogue.Eighth
