-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_collision_to_quotient_invariant
-- name    : Couret.InterIA.Catalogue.collision_to_quotient_invariant
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:17.108943+00:00
-- url     : https://prove2.me/theorems/750f5558-2e0b-4200-992f-6525bc4d8204
-- title:
--   collision to quotient invariant
-- statement:
--   For every positive integer $m$ and finite subsets $S,T$ of $R=ℤ/(2m)ℤ$, assume $|S|=|T|=4$, that for every $z∈R$ the numbers of ordered pairs in $S²$ and $T²$ summing to $z$ agree, and that there are no unit $u∈R$ and $v∈R$ with $uS+v=T$. There exist $t∈\{0,m\}$ and $a,b∈R$ such that, writing $T_t=T+t$, Let $π: R→ℤ/mℤ$ be reduction modulo $m$, let $e_y$ denote the group-ring element with coefficient $1$ at $y$ and $0$ elsewhere, and set $F=∑_{c∈S∩T_t}e_{π(c)}+e_{π(a)}+e_{π(b)}$ in $ℤ[ℤ/mℤ]$. For $δ=π(b-a)$ one has $δ≠0$, $F=e_δF$, the sum of the coefficients of $F$ is $4$, and every coefficient is nonnegative. No further relation between $a,b$ and the set differences is asserted here.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientResidual.lean, lines 132–151; source file SHA-256 29c3ae2cbecdf646a84bc5ab6931803cdc7db5ad9705778c5cd73f60b149f4bb; theorem Couret.InterIA.Catalogue.collision_to_quotient_invariant

import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_normal_form_quotient_invariant
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Definitions.Def_Couret_L4Assembly_154a326d9c14

set_option autoImplicit false
namespace Couret.InterIA.Catalogue
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing
open Couret.InterIA.Projection

theorem collision_to_quotient_invariant (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧ ∃ a b,
      projection m (b-a) ≠ 0 ∧
      residual m (S ∩ T.image (fun x => x+t)) a b=
        A (projection m (b-a))*residual m (S ∩ T.image (fun x => x+t)) a b ∧
      (residual m (S ∩ T.image (fun x => x+t)) a b).sum (fun _ n => n)=4 ∧
      (∀ z, 0 ≤ (residual m (S ∩ T.image (fun x => x+t)) a b).coeff z) := by sorry


end Couret.InterIA.Catalogue
