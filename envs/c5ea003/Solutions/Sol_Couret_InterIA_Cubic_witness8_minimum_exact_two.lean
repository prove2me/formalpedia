-- Prove2me | solution 1 for Couret.InterIA.Cubic.witness8_minimum_exact_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:18.175586+00:00
-- url     : https://prove2.me/submissions/0893b6da-b419-4cdd-85f9-b5dfa05083c7

import Definitions.Def_Couret_CubicWitness8_775020fe3011
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
import Theorems.Thm_Couret_InterIA_Cubic_cyclic_four_two_cubic_probes
import Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres



theorem witness8_card : ∀ i : Fin 4, (witness8 i).card=4 := by decide

theorem witness8_injective : Function.Injective witness8 := by decide

theorem witness8_common_square : ∀ (i : Fin 4) (z : ZMod 8),
    orderedSquare (witness8 i) z=orderedSquare (witness8 0) z := by decide

theorem witness8_no_single_coordinate : ∀ z : ZMod 8, ∃ i j : Fin 4,
    i≠j ∧ orderedCube (witness8 i) z=orderedCube (witness8 j) z := by decide



theorem witness8_mem_fibre (i : Fin 4) : witness8 i ∈ cyclicFourFibre 8 (witness8 0) :=
  ⟨witness8_card i,fun z => (witness8_common_square i z).symm⟩

theorem cubic_two_probes_necessary : ¬ ∃ z : ZMod 8,
    Separates realCube (cyclicFourFibre 8 (witness8 0)) {z} := by
  rintro ⟨z,hz⟩
  obtain ⟨i,j,hij,he⟩ := witness8_no_single_coordinate z
  have hs : witness8 i=witness8 j := by
    apply hz (witness8 i) (witness8_mem_fibre i) (witness8 j) (witness8_mem_fibre j)
    intro w hw
    have hwz : w=z := Finset.mem_singleton.mp hw
    subst w
    change (orderedCube (witness8 i) z : ℝ)=(orderedCube (witness8 j) z : ℝ)
    rw [he]
  exact hij (witness8_injective hs)

theorem witness8_probes_card_ge_two (Q : Finset (ZMod 8))
    (hQ : Separates realCube (cyclicFourFibre 8 (witness8 0)) Q) : 2≤Q.card := by
  by_contra! h
  have hc : Q.card≤1 := by omega
  obtain ⟨z,hz⟩ := Finset.card_le_one_iff_subset_singleton.mp hc
  apply cubic_two_probes_necessary
  refine ⟨z,?_⟩
  intro A hA B hB he
  apply hQ A hA B hB
  intro w hw
  exact he w (hz hw)

theorem p2m_local_witness8_minimum_exact_two : ∃ Q : Finset (ZMod 8), Q.card=2 ∧
    Separates realCube (cyclicFourFibre 8 (witness8 0)) Q := by
  obtain ⟨Q,hcard,hsep⟩ := cyclic_four_two_cubic_probes 8 (by decide)
    (witness8 0) (witness8_card 0)
  exact ⟨Q,Nat.le_antisymm hcard (witness8_probes_card_ge_two Q hsep),hsep⟩

end Couret.InterIA.Cubic

theorem solution : @Exists.{1} (Finset.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) fun Q =>
  And
    (@Eq.{1} Nat (@Finset.card.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) Q)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Couret.InterIA.Cubic.Separates.{0, 0}
      (Finset.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (@Couret.InterIA.Cubic.realCube.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
        (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (Couret.InterIA.Fibres.cyclicFourFibre (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
        (Couret.InterIA.Cubic.witness8
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))))
      Q) := @_root_.Couret.InterIA.Cubic.p2m_local_witness8_minimum_exact_two

