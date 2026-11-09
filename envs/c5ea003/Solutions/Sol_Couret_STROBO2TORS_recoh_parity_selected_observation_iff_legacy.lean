-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_selected_observation_iff_legacy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:27.937278+00:00
-- url     : https://prove2.me/submissions/1db480c0-a663-48c6-a9ae-615bc3a01d24

import Aesop
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517

set_option autoImplicit false

/-!
Coefficient decoding from the compact parity family.

The generic bridge uses a proved cover modulo two-torsion, the historical
sign-recovery specification and the exact integer observation checker.
The new candidate construction is an image of the parity family, not the
historical edge-triple enumeration. Definitions enumerate neither G nor
its two-torsion subgroup. Complex values occur only in the specification.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2













variable [Fintype I]







section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





















































/-- Relabelling slots preserves the complete semantic observation. -/
theorem p2m_local_recoh_parity_selected_observation_iff_legacy
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    recohObservation (recohParitySelectedObservedBank q entries) S =
        recohParitySelectedTypedObservation q entries terms ↔
      recohObservation (recohSelectedObservedBank q entries) S =
        recohSelectedTypedObservation q entries
          (recohParitySelectedLegacyTerms q entries terms) := by
  constructor
  · intro h
    apply Prod.ext
    · have hfst := congrArg Prod.fst h
      exact hfst
    · funext i
      have hi := congrFun (congrArg Prod.snd h)
        ((recohParitySelectedBankEquiv q entries).symm i)
      change recohSupportProbe (recohSelectedObservedBank q entries
        (recohParitySelectedBankEquiv q entries
          ((recohParitySelectedBankEquiv q entries).symm i))) S =
        recohCoefficientValue (recohSelectedBankRoot q entries
          (recohParitySelectedBankEquiv q entries
            ((recohParitySelectedBankEquiv q entries).symm i)))
          (terms ((recohParitySelectedBankEquiv q entries).symm i)) at hi
      simpa only [Equiv.apply_symm_apply, recohSelectedTypedObservation,
        recohParitySelectedLegacyTerms] using hi
  · intro h
    apply Prod.ext
    · have hfst := congrArg Prod.fst h
      exact hfst
    · funext i
      have hi := congrFun (congrArg Prod.snd h) (recohParitySelectedBankEquiv q entries i)
      change recohSupportProbe (recohSelectedObservedBank q entries
        (recohParitySelectedBankEquiv q entries i)) S =
        recohCoefficientValue (recohSelectedBankRoot q entries
          (recohParitySelectedBankEquiv q entries i))
          (terms ((recohParitySelectedBankEquiv q entries).symm
            (recohParitySelectedBankEquiv q entries i))) at hi
      simpa only [Equiv.symm_apply_apply, recohParitySelectedTypedObservation,
        recohParitySelectedObservedBank, recohParitySelectedBankRoot] using hi















end CyclicSelected

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms)
  (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  Iff
    (@Eq.{1}
      (Prod.{0, 0} (((i : Fin d) → ZMod (q i)) → Nat)
        (@Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Complex))
      (@Couret.STROBO2TORS.recohObservation.{0, 0} ((i : Fin d) → ZMod (q i))
        (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
          @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
        (fun a b =>
          @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
            (Fin.fintype d) a b)
        (@Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries)
        (@Couret.STROBO2TORS.recohParitySelectedObservedBank d q inst entries) S)
      (@Couret.STROBO2TORS.recohParitySelectedTypedObservation d q inst entries terms))
    (@Eq.{1}
      (Prod.{0, 0} (((i : Fin d) → ZMod (q i)) → Nat)
        (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Complex))
      (@Couret.STROBO2TORS.recohObservation.{0, 0} ((i : Fin d) → ZMod (q i))
        (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
          @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
        (fun a b =>
          @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
            (Fin.fintype d) a b)
        (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
        (@Couret.STROBO2TORS.recohSelectedObservedBank d q inst entries) S)
      (@Couret.STROBO2TORS.recohSelectedTypedObservation d q inst entries
        (@Couret.STROBO2TORS.recohParitySelectedLegacyTerms d q inst entries terms))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_selected_observation_iff_legacy

