-- Prove2me | Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
-- name    : Couret_AntipodalFibres_0fc966ab17b4
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:52.70327+00:00
-- url     : https://prove2.me/theorems/893c0a8e-2418-466e-b2aa-bdd43f02d756
-- title:
--   Antipodal pairs and their finite families
-- statement:
--   For an abelian group $G$ and $h,x\in G$, define $$F_h(x)=\{x,x+h\},\qquad\mathcal F_h(D)=\{F_h(x):x\in D\}$$ for a finite support $D$. The bundle includes structural facts about these fibres under a nonzero half-turn, including disjointness and cardinality calculations, for use in four-point support decompositions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/AntipodalFibres.lean; source file SHA-256 9a1dfe7f920807e73cc1298e40bc46156ea44c37309efcb5a094afaf09a600a4

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def fibre (h x : G) : Finset G := {x, x+h}

def fibres (h : G) (D : Finset G) : Finset (Finset G) :=
  D.image (fibre h)

theorem fibre_card (h x : G) (hh : h ≠ 0) : (fibre h x).card = 2 := by
  apply Finset.card_pair
  intro he
  exact hh (add_left_cancel (by simpa using he.symm : x+h=x+0))

theorem fibre_partner (h x : G) (hh2 : h+h=0) : fibre h (x+h)=fibre h x := by
  have he : (x+h)+h=x := by rw [add_assoc,hh2,add_zero]
  simp [fibre,he,Finset.pair_comm]

theorem fibre_eq_of_mem (h x y : G) (hh2 : h+h=0)
    (hy : y ∈ fibre h x) : fibre h y=fibre h x := by
  simp only [fibre,mem_insert,mem_singleton] at hy
  rcases hy with rfl|rfl
  · rfl
  · exact fibre_partner h x hh2

theorem fibres_pairwise_disjoint (h : G) (hh2 : h+h=0) (D : Finset G) :
    (fibres h D : Set (Finset G)).PairwiseDisjoint id := by
  intro A hA B hB hne
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hB
  apply Finset.disjoint_left.mpr
  intro z hz hzy
  exact hne ((fibre_eq_of_mem h x z hh2 hz).symm.trans
    (fibre_eq_of_mem h y z hh2 hzy))

theorem fibres_union (h : G) (D : Finset G)
    (hstable : ∀ x ∈ D, x+h ∈ D) : (fibres h D).biUnion id = D := by
  ext z
  constructor
  · intro hz
    obtain ⟨A,hA,hzA⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
    simp only [id_eq,fibre,mem_insert,mem_singleton] at hzA
    rcases hzA with rfl|rfl
    · exact hx
    · exact hstable x hx
  · intro hz
    exact Finset.mem_biUnion.mpr ⟨fibre h z, Finset.mem_image.mpr ⟨z,hz,rfl⟩,
      by simp [fibre]⟩

theorem twice_fibres_card (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (D : Finset G) (hstable : ∀ x ∈ D, x+h ∈ D) :
    2*(fibres h D).card = D.card := by
  have hc := Finset.card_biUnion (fibres_pairwise_disjoint h hh2 D)
  rw [fibres_union h D hstable] at hc
  have hs : ∑ A ∈ fibres h D, A.card = ∑ _A ∈ fibres h D, 2 := by
    apply Finset.sum_congr rfl
    intro A hA
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
    exact fibre_card h x hh
  simp only [id_eq] at hc
  rw [hs] at hc
  simpa [Nat.mul_comm] using hc.symm





end Couret.InterIA.Fibres


