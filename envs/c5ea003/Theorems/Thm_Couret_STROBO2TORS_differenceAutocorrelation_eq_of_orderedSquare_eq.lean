-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_differenceAutocorrelation_eq_of_orderedSquare_eq
-- name    : Couret.STROBO2TORS.differenceAutocorrelation_eq_of_orderedSquare_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:42.424209+00:00
-- url     : https://prove2.me/theorems/64609390-8dc3-4bbe-add6-c1feb06e89af
-- title:
--   Equal labelled ordered squares imply homometry
-- statement:
--   Let G be an abelian group, Q_S(z)=#{(x,y) in S^2:x+y=z}, D_S(z)=#{(x,y) in S^2:x-y=z}, and P_S(chi)=sum_(x in S)chi(x), all unnormalized and retaining diagonals. Assume G finite. For arbitrary finite supports S,T, $$Q_S=Q_T\Longrightarrow D_S=D_T.$$ Equality is pointwise in the labelled group element and includes all multiplicities and diagonal terms.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/41a2ef6f6ae6f6a26b3d630d365ad404fd97fe42/research/strobo-2tors-2026-10-12/lean/StroboHomometry.lean#L103-L118, lines 103–118; source file SHA-256 d425a917138d22db0e9336b5a0dc3446107f7fd9eaaac85386bc9bdfb4cba274; theorem Couret.STROBO2TORS.differenceAutocorrelation_eq_of_orderedSquare_eq

import Aesop
import Definitions.Def_Couret_StroboHomometry_90864170804d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Classical Fourier implication, made explicit for the existing STROBO observable:
equal labelled ordered convolution squares imply equal difference multiplicities.
No converse and no novelty claim. See Lev (2004), section 3, Problem 2, p. 5,
and Riley Casper's observation of 2026-10-15.
-/

open scoped BigOperators ComplexConjugate

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]

theorem differenceAutocorrelation_eq_of_orderedSquare_eq (S T : Finset G)
    (h : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    ∀ z : G, differenceAutocorrelation S z = differenceAutocorrelation T z := by sorry






end Finite



end Couret.STROBO2TORS
