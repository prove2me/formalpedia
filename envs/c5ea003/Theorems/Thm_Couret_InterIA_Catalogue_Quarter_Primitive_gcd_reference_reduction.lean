-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_gcd_reference_reduction
-- name    : Couret.InterIA.Catalogue.Quarter.Primitive.gcd_reference_reduction
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:20.047757+00:00
-- url     : https://prove2.me/theorems/368714ee-34d0-41e5-8176-d7c862191dc3
-- title:
--   Gcd reduction to reference patterns
-- statement:
--   For every positive natural $q$ and $x\in R=\mathbb Z/(4q)\mathbb Z$ outside $\{0,q,2q,3q\}$, suppose no unit $u$ and $v\in R$ carry $A_q(x)=\{0,q,x,x+2q\}$ to $B_q(x)=\{0,q,x+q,x+3q\}$. There exist naturals $d,b,a$ with $d>0$, $b>0$, $q=db$, $\operatorname{val}(x)=da$, $\gcd(a,b)=1$ and $b\bmod4=2$ such that the images of $A_b(a)$ and $B_b(a)$ under $z\mapsto d\operatorname{val}(z)$ modulo $4q$ equal $A_q(x)$ and $B_q(x)$ respectively; furthermore, there exist a unit $u$ modulo $4b$ and $v\in\mathbb Z/(4b)\mathbb Z$ carrying the pair $(A_b(a),B_b(a))$ to $(A_b(1),B_b(1))$ in the same order or the opposite order. Here for every positive $j$, $A_j(y)=\{0,j,y,y+2j\}$ and $B_j(y)=\{0,j,y+j,y+3j\}$ in $\mathbb Z/(4j)\mathbb Z$, and $\operatorname{val}$ denotes the least nonnegative representative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveNormalisation.lean, lines 67–79; source file SHA-256 887d1f22b7114913eff0206bd9fb0b0b10e19d86cf09f8c53729d69597242304; theorem Couret.InterIA.Catalogue.Quarter.Primitive.gcd_reference_reduction

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_gcd_support_reduction
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_normalise_negative
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_unit_quarter_sign
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter.AffineCriterion

theorem gcd_reference_reduction (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (hna : ¬ AffineEquivalent (patternA q x) (patternB q x)) :
    ∃ d b a : ℕ, 0 < d ∧ 0 < b ∧ q=d*b ∧ x.val=d*a ∧ a.Coprime b ∧ b%4=2 ∧
      (patternA b (a : ZMod (4*b))).image (dilate (4*q) d)=patternA q x ∧
      (patternB b (a : ZMod (4*b))).image (dilate (4*q) d)=patternB q x ∧
      ∃ u : (ZMod (4*b))ˣ, ∃ v : ZMod (4*b),
        ((patternA b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternA b 1 ∧
         (patternB b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternB b 1) ∨
        ((patternA b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternB b 1 ∧
         (patternB b (a : ZMod (4*b))).image (fun z => (u : ZMod (4*b))*z+v)=patternA b 1) := by sorry


end Couret.InterIA.Catalogue.Quarter.Primitive
