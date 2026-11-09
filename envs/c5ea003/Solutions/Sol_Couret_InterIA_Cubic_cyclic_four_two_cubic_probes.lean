-- Prove2me | solution 1 for Couret.InterIA.Cubic.cyclic_four_two_cubic_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:49.301919+00:00
-- url     : https://prove2.me/submissions/8d23f966-b25b-4ea0-8873-b8a00f6cfdc8

import Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Cubic_small_family_probes
import Theorems.Thm_Couret_InterIA_Cubic_square_cube_support_injective
import Theorems.Thm_Couret_InterIA_Cubic_two_simple_cubic_probes
import Theorems.Thm_Couret_InterIA_Fibres_antipodal_free_four_ne_half_translate
import Definitions.Def_Couret_CubicSupport_513df21f9351
import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres



theorem realCube_injOn_fibre (n : ℕ) (hn : 0<n) (S : Finset (ZMod n)) :
    Set.InjOn realCube (cyclicFourFibre n S) := by
  intro A hA B hB he
  apply square_cube_support_injective n hn A B
  · intro z
    exact (hA.2 z).symm.trans (hB.2 z)
  · intro z
    have h := congrFun he z
    change (orderedCube A z : ℝ)=(orderedCube B z : ℝ) at h
    exact_mod_cast h



theorem p2m_local_cyclic_four_two_cubic_probes (n : ℕ) (hn : 0<n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    ∃ Q : Finset (ZMod n), Q.card≤2 ∧ Separates realCube (cyclicFourFibre n S) Q := by
  classical
  have hi := realCube_injOn_fibre n hn S
  rcases Nat.even_or_odd n with he|ho
  · obtain ⟨m,hm⟩ := he
    have hn2 : n=2*m := by omega
    clear hm
    subst n
    have hm : 0<m := by omega
    rcases even_four_support_cases m hm S hS with hf|hs|⟨C,a,hC,hf,hd,hSe⟩
    · apply small_family_probes realCube (cyclicFourFibre (2*m) S) hi
      right
      rw [show cyclicFourFibre (2*m) S={S,halfShift m S} from
        antipodal_free_four_fibre_eq_pair m hm S hS hf]
      exact Set.ncard_pair (antipodal_free_four_ne_half_translate m S hS hf)
    · exact small_family_probes realCube _ hi (stable_four_fibre_ncard m hm S hS hs)
    · rw [hSe]
      exact two_simple_cubic_probes m hm C a hC hf hd
  · apply small_family_probes realCube (cyclicFourFibre n S) hi
    left
    rw [odd_four_fibre_singleton n ho S hS,Set.ncard_singleton]

end Couret.InterIA.Cubic

theorem solution : ∀ (n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (S : Finset.{0} (ZMod n)),
      @Eq.{1} Nat (@Finset.card.{0} (ZMod n) S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Exists.{1} (Finset.{0} (ZMod n)) fun Q =>
          And
            (@LE.le.{0} Nat instLENat (@Finset.card.{0} (ZMod n) Q)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Couret.InterIA.Cubic.Separates.{0, 0} (Finset.{0} (ZMod n)) (ZMod n)
              (@Couret.InterIA.Cubic.realCube.{0} (ZMod n)
                (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                (ZMod.decidableEq n))
              (Couret.InterIA.Fibres.cyclicFourFibre n S) Q) := @_root_.Couret.InterIA.Cubic.p2m_local_cyclic_four_two_cubic_probes

