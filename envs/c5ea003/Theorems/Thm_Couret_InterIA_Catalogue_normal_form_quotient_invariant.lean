-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_normal_form_quotient_invariant
-- name    : Couret.InterIA.Catalogue.normal_form_quotient_invariant
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:49.400191+00:00
-- url     : https://prove2.me/theorems/70f411f6-c95e-40b6-b60d-247f10a56b33
-- title:
--   Quotient invariant of a normal form
-- statement:
--   For every positive natural $m$ and finite subsets $S,T\subseteq R=\mathbb Z/(2m)\mathbb Z$, suppose $|S\cap T|=2$, there exist $a_0,b_0\in R$ with $S\setminus T=\{a_0,a_0+m\}$ and $T\setminus S=\{b_0,b_0+m\}$, and the ordered-pair sum counts of $S,T$ agree everywhere. There exist $a,b\in R$ such that $\pi(b-a)\ne0$, $F=X^{\pi(b-a)}F$, the sum of all coefficients of $F$ is $4$, and every coefficient of $F$ is nonnegative, where $\pi$ is reduction modulo $m$, $F=\sum_{c\in S\cap T}X^{\pi(c)}+X^{\pi(a)}+X^{\pi(b)}$ belongs to $\mathbb Z[\mathbb Z/m\mathbb Z]$, and $X^yX^z=X^{y+z}$. The conclusion does not state that these witnesses $a,b$ reconstruct the two set differences.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientResidual.lean, lines 89–130; source file SHA-256 29c3ae2cbecdf646a84bc5ab6931803cdc7db5ad9705778c5cd73f60b149f4bb; theorem Couret.InterIA.Catalogue.normal_form_quotient_invariant

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
import Theorems.Thm_Couret_InterIA_Catalogue_residual_equation
import Theorems.Thm_Couret_InterIA_Catalogue_residual_four_atoms
import Theorems.Thm_Couret_InterIA_Catalogue_residual_invariant
import Definitions.Def_Couret_L4Assembly_154a326d9c14

set_option autoImplicit false
namespace Couret.InterIA.Catalogue
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing
open Couret.InterIA.Projection

theorem normal_form_quotient_invariant (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m)))
    (hn : Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∃ a b, projection m (b-a) ≠ 0 ∧
      residual m (S ∩ T) a b=A (projection m (b-a))*residual m (S ∩ T) a b ∧
      (residual m (S ∩ T) a b).sum (fun _ n => n)=4 ∧
      (∀ z, 0 ≤ (residual m (S ∩ T) a b).coeff z) := by sorry




end Couret.InterIA.Catalogue
