-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_sign_decoder_singleton
-- name    : Couret.STROBO2TORS.recoh_noisy_sign_decoder_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:28:39.809389+00:00
-- url     : https://prove2.me/theorems/0cc6c240-44bf-479f-bd3d-65c815593a3e
-- title:
--   End-to-end noisy decoding returns the true support
-- statement:
--   For a rational pair z=(a,b), write V(z)=a+bi. Let G be an abelian group, H=G[2], and P_i(B)=sum_(x in B)chi_i(x) for a bank of complex additive characters. An additive equivalence e:H≃(J→F_2) supplies binary coordinates. The rational sign test accepts exactly when the radius r is nonnegative and the rational squared distance from observed to predicted is at most r^2. Recovery translates each representative by the H-element obtained from its sign bits via e inverse. Let I be finite, index:J→I select binary slots, b:Finset(G)→I→Q^2 be predictions, o:I→Q^2 observations, and r a rational radius. The sign decoder first recovers candidates from selected slots, then keeps exactly those passing the rational ball test at every full-bank slot. Assume G finite, R⊆F(S), and S is an H-translate of some B in R. Require the selected bank coordinates to satisfy chi_(index j)(u)=(-1)^(e(u)_j). Let epsilon,eta be real with eta≥0 and r≥0. Assume the full bank separates F(S) by 2; every selected probe of every B in R has amplitude at least 1; all full-bank predictions of every T in F(S) have error at most eta; and the observations have error at most epsilon from the full probes of S. If $$\varepsilon+\eta\le r,\qquad2(r+\eta)<2,$$ then $$D(R,e,index,b,o,r)=\{S\}.$$ No separate epsilon≥0 or |S|=3 premise is imposed; the stated coverage hypotheses supply the relevant support structure.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisySignRecovery.lean#L228-L273, lines 228–273; source file SHA-256 0b99604778196eef3e1a2e7f4520b571c7f705ced9a9268c1833a15086c9a9a4; theorem Couret.STROBO2TORS.recoh_noisy_sign_decoder_singleton

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recover_support_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recovered_candidates_square_sound
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_singleton
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

theorem recoh_noisy_sign_decoder_singleton [Fintype G]
    {I : Type*} [Fintype I]
    (bank : I → AddChar G ℂ) (S : Finset G) (representatives : Finset (Finset G))
    (hrepresentatives : representatives ⊆ squareFibre S)
    (hcover : ∃ B ∈ representatives, OrdinaryPartner B S)
    (e : H₂ ≃+ (J → ZMod 2)) (index : J → I)
    (hcoord : ∀ (u : H₂) (j : J), bank (index j) (u : G) = if e u j = 0 then 1 else -1)
    (predicted : Finset G → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) (ε η : ℝ)
    (hradius : 0 ≤ radius) (hη : 0 ≤ η)
    (hsep : RecohProbeSeparated bank (squareFibre S) 2)
    (hamplitude : ∀ B ∈ representatives, ∀ j, 1 ≤ ‖recohSupportProbe (bank (index j)) B‖)
    (hpred : ∀ T ∈ squareFibre S, ∀ i,
      ‖recohRationalComplexValue (predicted T i) - recohSupportProbe (bank i) T‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) - recohSupportProbe (bank i) S‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : 2 * ((radius : ℝ) + η) < 2) :
    recohNoisySignDecoder representatives e index predicted observed radius = {S} := by sorry


end Couret.STROBO2TORS
