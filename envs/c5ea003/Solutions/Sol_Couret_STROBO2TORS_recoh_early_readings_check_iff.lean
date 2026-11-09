-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_early_readings_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:44.105582+00:00
-- url     : https://prove2.me/submissions/a6d16c9f-2962-4421-91e8-6ba58645902f

import Aesop
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_neg_iff
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5

set_option autoImplicit false

/-!
Early rejection of incompatible binary and ternary readings.

The bank index is J ⊕ K.  The intended cyclic bank uses prime two on J and
prime three on K.  The executable tests retain the supplied prime parameters;
their correctness uses explicit primary-representation contracts and the two
roles on G[2]: signs on J, trivial character values on K.

Binary observations must equal the representative reading or its negative;
ternary observations must equal the representative reading.  These are exact
integer-coefficient comparisons.  A final accepted recovered support always
passes these early tests, without nonvanishing or cardinality assumptions.
Combining them with the early square check therefore preserves the answer of
the full coefficient backend.  This proves an order of typed mathematical
operations, not the external Python parser, cache, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G J K : Type*} [AddCommGroup G] [DecidableEq G]
variable [Fintype J] [Fintype K]

local notation "H₂" => recohTorsionSubgroup (G := G) 2



omit [DecidableEq G] in
/-- Exact semantics of the two early reading tests. -/
theorem p2m_local_recoh_early_readings_check_iff
    (p k : J ⊕ K → ℕ) (enc : J ⊕ K → Finset G → List ℕ)
    (obsTerms : J ⊕ K → RecohSparseTerms) (B : Finset G)
    (bank : J ⊕ K → AddChar G ℂ) (ζ obs : J ⊕ K → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i) :
    recohEarlyReadingsCheck p k enc obsTerms B = true ↔
      (∀ j : J, obs (Sum.inl j) = recohSupportProbe (bank (Sum.inl j)) B ∨
        obs (Sum.inl j) = -recohSupportProbe (bank (Sum.inl j)) B) ∧
      (∀ j : K, obs (Sum.inr j) = recohSupportProbe (bank (Sum.inr j)) B) := by
  have hpos (i : J ⊕ K) :
      recohCoefficientMatch (p i) (k i) (enc i B) (obsTerms i) = true ↔
        obs i = recohSupportProbe (bank i) B := by
    rw [recoh_coefficient_match_iff (hp i) (k i) (hζ i) _ _ (hred i), henc, hobs]
    exact eq_comm
  have hneg (i : J ⊕ K) :
      recohCoefficientMatchNeg (p i) (k i) (enc i B) (obsTerms i) = true ↔
        obs i = -recohSupportProbe (bank i) B := by
    rw [recoh_coefficient_match_neg_iff (hp i) (k i) (hζ i) _ _ (hred i), henc, hobs]
    exact eq_comm
  simp only [recohEarlyReadingsCheck, Bool.and_eq_true, decide_eq_true_eq, hpos, hneg]













end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} {J : Type p2m_u_1} {K : Type p2m_u_2} [inst : AddCommGroup.{p2m_u_0} G]
  [inst_1 : Fintype.{p2m_u_1} J] [inst_2 : Fintype.{p2m_u_2} K] (p k : Sum.{p2m_u_1, p2m_u_2} J K → Nat)
  (enc : Sum.{p2m_u_1, p2m_u_2} J K → Finset.{p2m_u_0} G → List.{0} Nat)
  (obsTerms : Sum.{p2m_u_1, p2m_u_2} J K → Couret.STROBO2TORS.RecohSparseTerms) (B : Finset.{p2m_u_0} G)
  (bank :
    Sum.{p2m_u_1, p2m_u_2} J K →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : Sum.{p2m_u_1, p2m_u_2} J K → Complex),
  (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K), Nat.Prime (p i)) →
    (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K),
        @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K), Couret.STROBO2TORS.RecohCoefficientsReduced (p i) (k i) (obsTerms i)) →
        (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K),
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
          (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K),
              @Eq.{1} Complex (Couret.STROBO2TORS.recohCoefficientValue (ζ i) (obsTerms i)) (obs i)) →
            Iff
              (@Eq.{1} Bool
                (@Couret.STROBO2TORS.recohEarlyReadingsCheck.{p2m_u_0, p2m_u_1, p2m_u_2} G J K inst_1 inst_2 p k enc
                  obsTerms B)
                Bool.true)
              (And
                (∀ (j : J),
                  Or
                    (@Eq.{1} Complex (obs (@Sum.inl.{p2m_u_1, p2m_u_2} J K j))
                      (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (@Sum.inl.{p2m_u_1, p2m_u_2} J K j))
                        B))
                    (@Eq.{1} Complex (obs (@Sum.inl.{p2m_u_1, p2m_u_2} J K j))
                      (@Neg.neg.{0} Complex Complex.instNeg
                        (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst
                          (bank (@Sum.inl.{p2m_u_1, p2m_u_2} J K j)) B))))
                (∀ (j : K),
                  @Eq.{1} Complex (obs (@Sum.inr.{p2m_u_1, p2m_u_2} J K j))
                    (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (@Sum.inr.{p2m_u_1, p2m_u_2} J K j))
                      B))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_early_readings_check_iff

