-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_sign_decoder_card_le_representatives
-- name    : Couret.STROBO2TORS.recoh_noisy_sign_decoder_card_le_representatives
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:15.361755+00:00
-- url     : https://prove2.me/theorems/a9f1c9c0-96cb-4ab1-8d50-c3e2524c0c69
-- title:
--   The complete noisy decoder has at most the representative count
-- statement:
--   For a rational pair z=(a,b), write V(z)=a+bi. Let G be an abelian group, H=G[2], and P_i(B)=sum_(x in B)chi_i(x) for a bank of complex additive characters. An additive equivalence e:H≃(J→F_2) supplies binary coordinates. The rational sign test accepts exactly when the radius r is nonnegative and the rational squared distance from observed to predicted is at most r^2. Recovery translates each representative by the H-element obtained from its sign bits via e inverse. Let I be finite, index:J→I select binary slots, b:Finset(G)→I→Q^2 be predictions, o:I→Q^2 observations, and r a rational radius. The sign decoder first recovers candidates from selected slots, then keeps exactly those passing the rational ball test at every full-bank slot. For every finite representative family R, $$|D(R,e,index,b,o,r)|\le|R|.$$ No semantic accuracy, bank, or radius-sign hypotheses are required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisySignRecovery.lean#L192-L200, lines 192–200; source file SHA-256 0b99604778196eef3e1a2e7f4520b571c7f705ced9a9268c1833a15086c9a9a4; theorem Couret.STROBO2TORS.recoh_noisy_sign_decoder_card_le_representatives

import Aesop
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recovered_candidates_card_le
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3

set_option autoImplicit false

/-!
Noisy sign recovery from a list of square-fibre representatives.  Each
binary sign is recovered by one rational ball test, then transported through
the existing two-torsion coordinate equivalence.  At most one candidate is
created per representative, without enumerating the two-torsion subgroup.
The rational decoder in RecohNoisyUniqueness supplies the final tolerance
filter and uniqueness contract.
-/

namespace Couret.STROBO2TORS







variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

theorem recoh_noisy_sign_decoder_card_le_representatives {I : Type*} [Fintype I]
    (representatives : Finset (Finset G)) (e : H₂ ≃+ (J → ZMod 2))
    (index : J → I) (predicted : Finset G → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) :
    (recohNoisySignDecoder representatives e index predicted observed radius).card ≤
      representatives.card := by sorry






end Couret.STROBO2TORS
