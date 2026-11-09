-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_coefficient_observation_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:44.700389+00:00
-- url     : https://prove2.me/submissions/b19ce693-c57e-4390-8a68-d6d9fb26377a

import Aesop
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_readings_check_iff
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Exact observation checking from integer cyclotomic coefficients.

Observed readings are supplied directly as lists of pairs `(exponent,
integer coefficient)`.  No conversion from coefficients back to root lists
is used.  Complex values occur only in the interpretation and correctness
theorems; all checkers compare natural numbers and integer coefficients.

The range contract is sufficient for faithful evaluation.  The stronger
typed-format contract also excludes zero coefficients and repeated
exponents, matching the conditions inspected by Python `_read_coefficients`.
It does not certify JSON parsing, Python execution or sorting.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators





































variable {G : Type*} [AddCommGroup G] [DecidableEq G]







theorem p2m_local_recoh_coefficient_observation_check_iff {I : Type*} [Fintype I]
    (U : Finset G) (R : G → ℕ) (p k : I → ℕ)
    (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms) (S : Finset G)
    (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hterms : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i) :
    recohCoefficientObservationCheck U R p k enc obsTerms S = true ↔
      recohObservation bank S = (R, obs) := by
  rw [recohCoefficientObservationCheck, Bool.and_eq_true,
    recoh_sparse_square_check_iff U S R hR,
    recoh_coefficient_readings_check_iff p k enc obsTerms S bank ζ obs hp hζ hterms henc hobs]
  simp only [recohObservation, Prod.mk.injEq]





/-!
The coefficient checkers do not themselves establish support coverage,
primality, primitive-root identities or the interpretation of candidate
encodings.  Their correctness theorems display these contracts explicitly.
The observed coefficient values require no witness as a sum of three roots.
Such a representation, if it exists, is supplied by a successfully checked
candidate rather than assumed as an input encoding.

Typed lists may be arbitrarily long.  No constant or bit-complexity bound
for reading or checking observed input is asserted here.  In particular,
the twelve-position bound for comparing two normalized triples is not a
bound on arbitrary externally supplied coefficient lists.
-/


end Couret.STROBO2TORS

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {I : Type p2m_u_1}
  [inst_2 : Fintype.{p2m_u_1} I] (U : Finset.{p2m_u_0} G) (R : G → Nat) (p k : I → Nat)
  (enc : I → Finset.{p2m_u_0} G → List.{0} Nat) (obsTerms : I → Couret.STROBO2TORS.RecohSparseTerms)
  (S : Finset.{p2m_u_0} G)
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : I → Complex),
  (∀ (z : G),
      @Ne.{1} Nat (R z) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z) →
    (∀ (i : I), Nat.Prime (p i)) →
      (∀ (i : I),
          @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        (∀ (i : I), Couret.STROBO2TORS.RecohCoefficientsReduced (p i) (k i) (obsTerms i)) →
          (∀ (i : I),
              @Eq.{1} Complex
                (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                  (@List.map.{0, 0} Nat Complex
                    (fun x =>
                      @HPow.hPow.{0, 0, 0} Complex Nat Complex
                        (@instHPow.{0, 0} Complex Nat
                          (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                        (ζ i) x)
                    (enc i S)))
                (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S)) →
            (∀ (i : I), @Eq.{1} Complex (Couret.STROBO2TORS.recohCoefficientValue (ζ i) (obsTerms i)) (obs i)) →
              Iff
                (@Eq.{1} Bool
                  (@Couret.STROBO2TORS.recohCoefficientObservationCheck.{p2m_u_0, p2m_u_1} G inst inst_1 I inst_2 U R p
                    k enc obsTerms S)
                  Bool.true)
                (@Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex))
                  (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank S)
                  (@Prod.mk.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) R obs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_coefficient_observation_check_iff

