-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Periods_collision_periods
-- name    : Couret.InterIA.Catalogue.Periods.collision_periods
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:01.75106+00:00
-- url     : https://prove2.me/theorems/9f9063d8-e4d9-4158-9e41-651c7c2a74ec
-- title:
--   collision periods
-- statement:
--   For every positive integer $m$ and finite subsets $S,T$ of $R=ℤ/(2m)ℤ$, assume $|S|=|T|=4$, that for every $z∈R$ the numbers of ordered pairs in $S²$ and $T²$ summing to $z$ agree, and that there are no unit $u∈R$ and $v∈R$ with $uS+v=T$. There exists $t∈\{0,m\}$ such that, with $T_t=T+t$, its intersection has cardinality two, and its two respective set differences are $\{a,a+m\}$ and $\{b,b+m\}$ for some $a,b∈R$. Moreover there exist (independently quantified) $a,b∈R$ such that $δ=π(b-a)$ has additive order $2$ or $4$ and the following holds. Let $π: R→ℤ/mℤ$ be reduction modulo $m$, let $e_y$ denote the group-ring element with coefficient $1$ at $y$ and $0$ elsewhere, and set $F=∑_{c∈S∩T_t}e_{π(c)}+e_{π(a)}+e_{π(b)}$ in $ℤ[ℤ/mℤ]$. Then $F=e_δF$, the sum of all coefficients of $F$ is $4$, and every coefficient of $F$ is nonnegative.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientPeriods.lean, lines 84–104; source file SHA-256 bd9057bd807a1c77c8c1dc1a052c267cfc2bf47a18692508e9871acc4ea527c8; theorem Couret.InterIA.Catalogue.Periods.collision_periods

import Definitions.Def_Couret_QuotientPeriods_cf8d74422994
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Periods_residual_periods
import Theorems.Thm_Couret_InterIA_Catalogue_normal_form_quotient_invariant
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Periods
open Finset Couret.InterIA.Catalogue Couret.InterIA.Parity Couret.InterIA.Projection
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem collision_periods (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S (T.image (fun x => x+t)) ∧
      ∃ a b, (addOrderOf (projection m (b-a))=2 ∨ addOrderOf (projection m (b-a))=4) ∧
        residual m (S ∩ T.image (fun x => x+t)) a b=
          A (projection m (b-a))*residual m (S ∩ T.image (fun x => x+t)) a b ∧
        (residual m (S ∩ T.image (fun x => x+t)) a b).sum (fun _ n => n)=4 ∧
        (∀ z, 0 ≤ (residual m (S ∩ T.image (fun x => x+t)) a b).coeff z) := by sorry


end Couret.InterIA.Catalogue.Periods
