-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recover_support_eq
-- name    : Couret.STROBO2TORS.recoh_noisy_recover_support_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:48.273627+00:00
-- url     : https://prove2.me/theorems/7298b6ab-9ad2-4347-9d71-241072190432
-- title:
--   Noisy signs recover the exact two-torsion translation
-- statement:
--   For a rational pair z=(a,b), write V(z)=a+bi. Let G be an abelian group, H=G[2], and P_i(B)=sum_(x in B)chi_i(x) for a bank of complex additive characters. An additive equivalence e:H≃(J→F_2) supplies binary coordinates. The rational sign test accepts exactly when the radius r is nonnegative and the rational squared distance from observed to predicted is at most r^2. Recovery translates each representative by the H-element obtained from its sign bits via e inverse. Assume chi_i(u)=(-1)^(e(u)_i) for all u in H and i in J. Fix a finite representative B, u in H, prediction map b and observations o in rational pairs, rational r≥0 and real epsilon,eta. Assume every |P_i(B)|≥1, every ||V(b(B,i))-P_i(B)||≤eta, and every ||V(o_i)-P_i(B+u)||≤epsilon. Require epsilon+eta≤r and epsilon+(r+eta)<2. Then $$\operatorname{Recover}(e,b,o,r,B)=B+u.$$ No assumption that B has three elements or G is finite is imposed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisySignRecovery.lean#L94-L134, lines 94–134; source file SHA-256 0b99604778196eef3e1a2e7f4520b571c7f705ced9a9268c1833a15086c9a9a4; theorem Couret.STROBO2TORS.recoh_noisy_recover_support_eq

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_eq_translation
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_sign_same_correct
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

theorem recoh_noisy_recover_support_eq
    (bank : J → AddChar G ℂ) (e : H₂ ≃+ (J → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : J), bank i (u : G) = if e u i = 0 then 1 else -1)
    (predicted : Finset G → J → RecohRationalComplex)
    (observed : J → RecohRationalComplex) (radius : ℚ) (ε η : ℝ)
    (hradius : 0 ≤ radius) (B : Finset G) (u : H₂)
    (hamplitude : ∀ i, 1 ≤ ‖recohSupportProbe (bank i) B‖)
    (hpred : ∀ i, ‖recohRationalComplexValue (predicted B i) -
      recohSupportProbe (bank i) B‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (bank i) (translateSupport B (u : G))‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : ε + ((radius : ℝ) + η) < 2) :
    recohNoisyRecoverSupport e predicted observed radius B = translateSupport B (u : G) := by sorry














end Couret.STROBO2TORS
