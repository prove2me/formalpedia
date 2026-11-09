-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_coefficient_sign_bools_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:28.488054+00:00
-- url     : https://prove2.me/submissions/9e240e08-abf4-4887-820c-ccb75c9790eb

import Aesop
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_iff
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
The RECOH decoder with observed coefficients in the cyclotomic power basis.

The observed inputs are finite lists of exponent/integer-coefficient pairs,
as used by the Python observation format.  Candidate readings are generated
from root exponents and compared directly to those pairs.  No inverse map
from a coefficient polynomial to a list of roots is required.

The binary probes are selected inside the same full bank and use the same
observed inputs.  Their index type is arbitrary, allowing the actual subtype
of even cyclic coordinates rather than a noncomputable reindexing to Fin r.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2



omit [DecidableEq G] in
/-- The coefficient interface supplies the equality contract used for signs. -/
theorem p2m_local_recoh_coefficient_sign_bools_exact
    (index : J → I) (p k : I → ℕ)
    (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms)
    (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i B, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (B : Finset G) (j : J) :
    recohCoefficientSignBools index p k enc obsTerms B j = true ↔
      obs (index j) = recohSupportProbe (bank (index j)) B := by
  unfold recohCoefficientSignBools
  rw [recoh_coefficient_match_iff (hp (index j)) (k (index j))
    (hζ (index j)) _ _ (hred (index j)), henc, hobs]
  exact eq_comm

variable [Fintype I]







end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} {I : Type p2m_u_1} {J : Type p2m_u_2} [inst : AddCommGroup.{p2m_u_0} G] (index : J → I)
  (p k : I → Nat) (enc : I → Finset.{p2m_u_0} G → List.{0} Nat) (obsTerms : I → Couret.STROBO2TORS.RecohSparseTerms)
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : I → Complex),
  (∀ (i : I), Nat.Prime (p i)) →
    (∀ (i : I),
        @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      (∀ (i : I), Couret.STROBO2TORS.RecohCoefficientsReduced (p i) (k i) (obsTerms i)) →
        (∀ (i : I) (B : Finset.{p2m_u_0} G),
            @Eq.{1} Complex
              (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                (@List.map.{0, 0} Nat Complex
                  (fun x =>
                    @HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                      (ζ i) x)
                  (enc i B)))
              (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) B)) →
          (∀ (i : I), @Eq.{1} Complex (Couret.STROBO2TORS.recohCoefficientValue (ζ i) (obsTerms i)) (obs i)) →
            ∀ (B : Finset.{p2m_u_0} G) (j : J),
              Iff
                (@Eq.{1} Bool
                  (@Couret.STROBO2TORS.recohCoefficientSignBools.{p2m_u_0, p2m_u_1, p2m_u_2} G I J index p k enc
                    obsTerms B j)
                  Bool.true)
                (@Eq.{1} Complex (obs (index j))
                  (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index j)) B)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_coefficient_sign_bools_exact

