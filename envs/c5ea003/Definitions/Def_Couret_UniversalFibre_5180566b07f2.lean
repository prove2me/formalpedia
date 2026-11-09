-- Prove2me | Definitions.Def_Couret_UniversalFibre_5180566b07f2
-- name    : Couret_UniversalFibre_5180566b07f2
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:10:51.609415+00:00
-- url     : https://prove2.me/theorems/03dc21f8-4937-419a-bd1f-afac89e1908b
-- title:
--   Universal cyclic four-support square fibres
-- statement:
--   For $S\subseteq\mathbb Z/n\mathbb Z$, define
--
--   $$\mathcal F_4(S)=\{T:|T|=4,\ Q_T=Q_S\}.$$
--
--   The bundle also supplies the exhaustive support-shape split for even moduli into antipodal-free, half-turn-stable and two-simple cases, and the singleton fibre result for odd moduli. This is the common fibre interface for cyclic reconstruction and cardinality theorems.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/UniversalFibre.lean; source file SHA-256 3fd4ea1a66d36d491e106728a1774c805d3d0d2019820d42d877037a669e290b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_StableFibreLift_7567a251f927

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.Projection

/-- The original labelled four-point fibre, with a modulus-independent interface. -/
def cyclicFourFibre (n : ℕ) (S : Finset (ZMod n)) : Set (Finset (ZMod n)) :=
  {T | T.card=4 ∧ ∀ z, orderedSquare S z=orderedSquare T z}

/-- Exhaustiveness at the support level: no assumption about a collision partner. -/
theorem even_four_support_cases (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m)))
    (hS : S.card=4) :
    AntipodalFree m S ∨ (∀ x ∈ S, x+m ∈ S) ∨
      ∃ (C : Finset (ZMod (2*m))) (a : ZMod (2*m)),
        C.card=2 ∧ AntipodalFree m C ∧ Disjoint C (fibre (m : ZMod (2*m)) a) ∧
          S=C ∪ fibre (m : ZMod (2*m)) a := by
  classical
  by_cases hf : AntipodalFree m S
  · exact Or.inl hf
  · have hex : ∃ a ∈ S, a+(m : ZMod (2*m)) ∈ S := by
      by_contra hn
      apply hf
      intro x hx hxm
      exact hn ⟨x,hx,hxm⟩
    obtain ⟨a,ha,ham⟩ := hex
    let D := fibre (m : ZMod (2*m)) a
    let C := S \ D
    have hD : D ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact ha
      · exact Finset.mem_singleton.mp hx ▸ ham
    have hd : Disjoint C D := Finset.sdiff_disjoint
    have hSe : S=C ∪ D := (Finset.sdiff_union_of_subset hD).symm
    have hC : C.card=2 := by
      have hc := Finset.card_union_of_disjoint hd
      rw [← hSe,hS,fibre_card _ a (Couret.InterIA.L4.half_ne_zero m hm)] at hc
      omega
    by_cases hc : AntipodalFree m C
    · exact Or.inr (Or.inr ⟨C,a,hC,hc,hd,hSe⟩)
    · have hexC : ∃ b ∈ C, b+(m : ZMod (2*m)) ∈ C := by
        by_contra hn
        apply hc
        intro x hx hxm
        exact hn ⟨x,hx,hxm⟩
      obtain ⟨b,hb,hbm⟩ := hexC
      have hB : fibre (m : ZMod (2*m)) b ⊆ C := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl|hx
        · exact hb
        · exact Finset.mem_singleton.mp hx ▸ hbm
      have hCe : C=fibre (m : ZMod (2*m)) b :=
        (Finset.eq_of_subset_of_card_le hB (by rw [hC,fibre_card _ b (Couret.InterIA.L4.half_ne_zero m hm)])).symm
      refine Or.inr (Or.inl ?_)
      rw [hSe,hCe]
      intro x hx
      rcases Finset.mem_union.mp hx with hx|hx
      · exact Finset.mem_union.mpr (Or.inl (Couret.InterIA.IntersectionTwo.stable_pair_of_antipodal b m
          (Couret.InterIA.L4.half_add_half m) x hx))
      · exact Finset.mem_union.mpr (Or.inr (Couret.InterIA.IntersectionTwo.stable_pair_of_antipodal a m
          (Couret.InterIA.L4.half_add_half m) x hx))

theorem odd_four_fibre_singleton (n : ℕ) (hn : Odd n) (S : Finset (ZMod n)) (hS : S.card=4) :
    cyclicFourFibre n S={S} := by
  ext T
  constructor
  · intro hT
    exact Set.mem_singleton_iff.mpr (odd_cyclic_square_injective n hn S T hT.2).symm
  · intro hT
    rw [Set.mem_singleton_iff.mp hT]
    exact ⟨hS,fun _ => rfl⟩





end Couret.InterIA.Fibres


