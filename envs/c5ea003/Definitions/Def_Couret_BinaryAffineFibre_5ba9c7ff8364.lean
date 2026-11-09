-- Prove2me | Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
-- name    : Couret_BinaryAffineFibre_5ba9c7ff8364
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:58.029939+00:00
-- url     : https://prove2.me/theorems/74798168-b71d-4309-bf63-bf28d961b406
-- title:
--   Binary affine structure of cyclic four-support fibres
-- statement:
--   Finite supports are encoded by their indicators with values in $\mathbb F_2$. Symmetric difference becomes vector addition. For $n>0$ and a four-set $S\subseteq\mathbb Z/n\mathbb Z$, the indicators of all four-sets with the same ordered-square counts form an affine subspace of $\mathbb F_2^{\mathbb Z/n\mathbb Z}$.
--
--   The bundle constructs that affine subspace and an equivalence from its support fibre to its direction space by subtracting the indicator of $S$. This supplies the structure behind power-of-two cardinalities and binary probe reconstruction.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/BinaryAffineFibre.lean; source file SHA-256 b920a719a42974e083f8586678ffbb9bb518599a9505a50ad0279045bdd7b28a

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

/-- Labelled membership vector, over the field with two elements. -/
def binaryIndicator {α : Type*} [DecidableEq α] (S : Finset α) : α → ZMod 2 :=
  fun x => if x ∈ S then 1 else 0

theorem binaryIndicator_injective {α : Type*} [DecidableEq α] :
    Function.Injective (binaryIndicator : Finset α → α → ZMod 2) := by
  intro S T he
  ext x
  have hx := congrFun he x
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp_all [binaryIndicator]

theorem binaryIndicator_xor {α : Type*} [DecidableEq α] (S T : Finset α) :
    binaryIndicator (symmDiff S T)=binaryIndicator S+binaryIndicator T := by
  funext x
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
    simp [binaryIndicator,Finset.mem_symmDiff,hs,ht]
  all_goals decide

theorem binary_vector_sub_eq_add {α : Type*} (u v : α → ZMod 2) : u-v=u+v := by
  funext x
  exact ZModModule.sub_eq_add (u x) (v x)

/-- Affineness is constructed from actual membership vectors and proved ternary closure. -/
def cyclicFibreAffine (n : ℕ) (hn : 0 < n) (S : Finset (ZMod n)) (hS : S.card=4) :
    AffineSubspace (ZMod 2) (ZMod n → ZMod 2) where
  carrier := binaryIndicator '' cyclicFourFibre n S
  smul_vsub_vadd_mem := by
    intro c p q r hp hq hr
    obtain ⟨T,hT,rfl⟩ := hp
    obtain ⟨U,hU,rfl⟩ := hq
    obtain ⟨V,hV,rfl⟩ := hr
    fin_cases c
    · change (0 : ZMod 2) • (binaryIndicator T-binaryIndicator U)+binaryIndicator V ∈ _
      rw [zero_smul,zero_add]
      exact ⟨V,hV,rfl⟩
    · change (1 : ZMod 2) • (binaryIndicator T-binaryIndicator U)+binaryIndicator V ∈ _
      rw [one_smul,binary_vector_sub_eq_add]
      refine ⟨symmDiff (symmDiff T U) V,cyclic_four_fibre_xor_closed n hn S hS T hT U hU V hV,?_⟩
      rw [binaryIndicator_xor,binaryIndicator_xor]



theorem binaryIndicator_base_mem (n : ℕ) (hn : 0 < n) (S : Finset (ZMod n)) (hS : S.card=4) :
    binaryIndicator S ∈ cyclicFibreAffine n hn S hS :=
  ⟨S,⟨hS,fun _ => rfl⟩,rfl⟩

noncomputable def fibreDirectionEquiv (n : ℕ) (hn : 0 < n) (S : Finset (ZMod n)) (hS : S.card=4) :
    cyclicFourFibre n S ≃ (cyclicFibreAffine n hn S hS).direction := by
  let A := cyclicFibreAffine n hn S hS
  have hbase : binaryIndicator S ∈ A := binaryIndicator_base_mem n hn S hS
  let f : cyclicFourFibre n S → A.direction := fun T =>
    ⟨binaryIndicator T.val-binaryIndicator S,
      AffineSubspace.vsub_mem_direction (show binaryIndicator T.val ∈ A from ⟨T.val,T.property,rfl⟩) hbase⟩
  apply Equiv.ofBijective f
  constructor
  · intro T U he
    have he' : binaryIndicator T.val-binaryIndicator S=binaryIndicator U.val-binaryIndicator S := congrArg Subtype.val he
    have hi := congrArg (fun w => w+binaryIndicator S) he'
    simp only [sub_add_cancel] at hi
    exact Subtype.ext (binaryIndicator_injective hi)
  · intro v
    obtain ⟨p,hp,hv⟩ := (AffineSubspace.mem_direction_iff_eq_vsub_right hbase v.val).mp v.property
    obtain ⟨T,hT,rfl⟩ := hp
    exact ⟨⟨T,hT⟩,Subtype.ext hv.symm⟩







end Couret.InterIA.Fibres


