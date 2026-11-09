-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_sparse_readings_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:22.413797+00:00
-- url     : https://prove2.me/submissions/d2b8e1a7-6c73-43a8-9bc2-3e856dc511a4

import Aesop
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_normalized_sparse_equal_iff
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Executable sparse checking of a full RECOH observation.

The ordered square is checked only on the supplied support of the observed
square together with sums of pairs in the proposed support.  Character
readings are checked by the certified integer-term comparator.  Neither
checker enumerates the ambient group or requires `Fintype G`.

The encodings of proposed and observed readings are input data.  Their
interpretation contracts, the primary orders, primitive roots and support
coverage are explicit hypotheses of correctness.  This module does not
certify a parser or construct those encodings from complex numbers.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]











omit [DecidableEq G] in
/-- Exactness of the reading test with explicit interpretation contracts
for both the proposed support and the observed readings. -/
theorem p2m_local_recoh_sparse_readings_check_iff {m : ℕ} (p k : Fin m → ℕ)
    (enc : Fin m → Finset G → List ℕ) (obsExp : Fin m → List ℕ)
    (S : Finset G) (bank : Fin m → AddChar G ℂ) (ζ obs : Fin m → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, ((obsExp i).map (ζ i ^ ·)).sum = obs i) :
    recohSparseReadingsCheck p k enc obsExp S = true ↔
      (fun i => recohSupportProbe (bank i) S) = obs := by
  simp only [recohSparseReadingsCheck, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    have hi := (recoh_normalized_sparse_equal_iff (hp i) (k i) (hζ i)
      (enc i S) (obsExp i)).mp (h i)
    simpa only [henc i, hobs i] using hi
  · intro h i
    apply (recoh_normalized_sparse_equal_iff (hp i) (k i) (hζ i)
      (enc i S) (obsExp i)).mpr
    rw [henc i, hobs i]
    exact congrFun h i






end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] {m : Nat} (p k : Fin m → Nat)
  (enc : Fin m → Finset.{p2m_u_0} G → List.{0} Nat) (obsExp : Fin m → List.{0} Nat) (S : Finset.{p2m_u_0} G)
  (bank :
    Fin m →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : Fin m → Complex),
  (∀ (i : Fin m), Nat.Prime (p i)) →
    (∀ (i : Fin m),
        @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      (∀ (i : Fin m),
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
        (∀ (i : Fin m),
            @Eq.{1} Complex
              (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                (@List.map.{0, 0} Nat Complex
                  (fun x =>
                    @HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                      (ζ i) x)
                  (obsExp i)))
              (obs i)) →
          Iff (@Eq.{1} Bool (@Couret.STROBO2TORS.recohSparseReadingsCheck.{p2m_u_0} G m p k enc obsExp S) Bool.true)
            (@Eq.{1} (Fin m → Complex) (fun i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S) obs) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_sparse_readings_check_iff

