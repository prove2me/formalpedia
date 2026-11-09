-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Parameters_collision_controlled_affine_forms
-- name    : Couret.InterIA.Catalogue.Parameters.collision_controlled_affine_forms
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:12:38.556672+00:00
-- url     : https://prove2.me/theorems/864383af-ecbb-43fc-8f70-0fe9cdd4c1f5
-- title:
--   collision controlled affine forms
-- statement:
--   For every positive integer $m$ and finite subsets $S,T$ of $R=ℤ/(2m)ℤ$, assume $|S|=|T|=4$, that for every $z∈R$ the numbers of ordered pairs in $S²$ and $T²$ summing to $z$ agree, and that there are no unit $u∈R$ and $v∈R$ with $uS+v=T$. There exists $t∈\{0,m\}$ such that, with $T_t=T+t$, either there exist a positive even integer $q$ with $2m=4q$, a unit $u∈R$, and $v,x∈R$, with $x∉\{0,q,2q,3q\}$, such that $uS+v=\{0,q,x,x+2q\}$ and $uT_t+v=\{0,q,x+q,x+3q\}$, or there exist an integer $q>0$ with $2m=8q$, a unit $u∈R$, and $v,c,d∈R$, with $c∈\{2q,6q\}$ and $d∈\{3q,7q\}$, such that $uS+v=\{c,d,0,4q\}$ and $uT_t+v=\{c,d,q,5q\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineParameterControls.lean, lines 80–91; source file SHA-256 b23f6d173f81bdcce0efd0f521f478b044082f8c922fd091f81c4bf2ca25e413; theorem Couret.InterIA.Catalogue.Parameters.collision_controlled_affine_forms

import Definitions.Def_Couret_AffineParameterControls_321393084939
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
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_collision_affine_forms
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_even_collision_eight_divides
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_affine_image_card
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_two_pattern_parameter_separation
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]

theorem collision_controlled_affine_forms (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      (TwoControlledForm m S (T.image (fun x => x+t)) ∨ FourAffineForm m S (T.image (fun x => x+t))) := by sorry


end Couret.InterIA.Catalogue.Parameters
