-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_sparse_observation_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:17.2678+00:00
-- url     : https://prove2.me/submissions/8623ab20-044b-469b-9993-063a16338f78

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_readings_check_iff
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















/-- The sparse executable checker is exactly the full labelled observation
filter.  It neither assumes finiteness of the ambient group nor certifies
the separately supplied encoding and support-coverage contracts. -/
theorem p2m_local_recoh_sparse_observation_check_iff {m : ℕ} (U : Finset G) (R : G → ℕ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) (S : Finset G)
    (bank : Fin m → AddChar G ℂ) (ζ obs : Fin m → ℂ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, ((obsExp i).map (ζ i ^ ·)).sum = obs i) :
    recohSparseObservationCheck U R p k enc obsExp S = true ↔
      recohObservation bank S = (R, obs) := by
  rw [recohSparseObservationCheck, Bool.and_eq_true,
    recoh_sparse_square_check_iff U S R hR,
    recoh_sparse_readings_check_iff p k enc obsExp S bank ζ obs hp hζ henc hobs]
  simp only [recohObservation, Prod.mk.injEq]


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {m : Nat}
  (U : Finset.{p2m_u_0} G) (R : G → Nat) (p k : Fin m → Nat) (enc : Fin m → Finset.{p2m_u_0} G → List.{0} Nat)
  (obsExp : Fin m → List.{0} Nat) (S : Finset.{p2m_u_0} G)
  (bank :
    Fin m →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : Fin m → Complex),
  (∀ (z : G),
      @Ne.{1} Nat (R z) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z) →
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
            Iff
              (@Eq.{1} Bool
                (@Couret.STROBO2TORS.recohSparseObservationCheck.{p2m_u_0} G inst inst_1 m U R p k enc obsExp S)
                Bool.true)
              (@Eq.{p2m_u_0 + 1} (Prod.{p2m_u_0, 0} (G → Nat) (Fin m → Complex))
                (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, 0} G inst inst_1 (Fin m) bank S)
                (@Prod.mk.{p2m_u_0, 0} (G → Nat) (Fin m → Complex) R obs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_sparse_observation_check_iff

