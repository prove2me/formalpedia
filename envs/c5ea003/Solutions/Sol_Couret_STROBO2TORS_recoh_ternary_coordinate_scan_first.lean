-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_ternary_coordinate_scan_first
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:24.343389+00:00
-- url     : https://prove2.me/submissions/bf57af7f-1f78-459a-b45c-e13bacc039f7

import Aesop
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An executable coordinate selector for a supplied direction killed by three.
The search visits the labelled cyclic coordinates in increasing order and
returns the first nonzero coordinate whose modulus is divisible by three.
Only natural divisibility and equality in a cyclic group are tested.

The optional selector is defined on every input vector. The total selector
requires the direction to be nonzero and killed by three; its proof arguments
are erased during execution. Complex characters are used only to state the
semantic detection guarantee for the selected coordinate.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ)













/-- Every earlier label failed the selector's predicate. This certifies the
first-match behavior without comparing any character values. -/
theorem p2m_local_recoh_ternary_coordinate_scan_first
    (v : (i : Fin d) → ZMod (q i)) (labels : List (Fin d))
    (i : RecohPrimaryCoordinate q 3)
    (hs : recohTernaryCoordinateScan q v labels = some i) :
    ∃ before after : List (Fin d),
      labels = before ++ i.val :: after ∧
        ∀ j ∈ before, 3 ∣ q j → v j = 0 := by
  induction labels with
  | nil => simp [recohTernaryCoordinateScan] at hs
  | cons j rest ih =>
      by_cases h : 3 ∣ q j ∧ v j ≠ 0
      · have heq : (⟨j, h.1⟩ : RecohPrimaryCoordinate q 3) = i :=
          Option.some.inj (by simpa only [recohTernaryCoordinateScan, dif_pos h] using hs)
        cases heq
        exact ⟨[], rest, rfl, by simp⟩
      · obtain ⟨before, after, hrest, hbefore⟩ :=
          ih (by simpa only [recohTernaryCoordinateScan, dif_neg h] using hs)
        refine ⟨j :: before, after, by simp only [List.cons_append, hrest], ?_⟩
        intro k hk hk3
        rcases List.mem_cons.mp hk with rfl | hk
        · by_contra hne
          exact h ⟨hk3, hne⟩
        · exact hbefore k hk hk3















variable [∀ i, NeZero (q i)]





















end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) (v : (i : Fin d) → ZMod (q i)) (labels : List.{0} (Fin d))
  (i : @Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  @Eq.{1}
      (Option.{0}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Couret.STROBO2TORS.recohTernaryCoordinateScan d q v labels)
      (@Option.some.{0}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        i) →
    @Exists.{1} (List.{0} (Fin d)) fun before =>
      @Exists.{1} (List.{0} (Fin d)) fun after =>
        And
          (@Eq.{1} (List.{0} (Fin d)) labels
            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin d)) (List.{0} (Fin d)) (List.{0} (Fin d))
              (@instHAppendOfAppend.{0} (List.{0} (Fin d)) (@List.instAppend.{0} (Fin d))) before
              (@List.cons.{0} (Fin d)
                (@Subtype.val.{1} (Fin d)
                  (fun i =>
                    @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q i))
                  i)
                after)))
          (∀ (j : Fin d),
            @Membership.mem.{0, 0} (Fin d) (List.{0} (Fin d)) (@List.instMembership.{0} (Fin d)) before j →
              @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q j) →
                @Eq.{1} (ZMod (q j)) (v j)
                  (@OfNat.ofNat.{0} (ZMod (q j)) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (ZMod (q j))
                      (@MulZeroClass.toZero.{0} (ZMod (q j))
                        (@instMulZeroClassOfSemiring.{0} (ZMod (q j))
                          (@CommSemiring.toSemiring.{0} (ZMod (q j))
                            (@CommRing.toCommSemiring.{0} (ZMod (q j)) (ZMod.commRing (q j))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_ternary_coordinate_scan_first

