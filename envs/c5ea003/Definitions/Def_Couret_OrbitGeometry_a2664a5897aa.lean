-- Prove2me | Definitions.Def_Couret_OrbitGeometry_a2664a5897aa
-- name    : Couret_OrbitGeometry_a2664a5897aa
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:08:13.768407+00:00
-- url     : https://prove2.me/theorems/bb72a754-ed54-4baf-a035-e5c5f1febb04
-- title:
--   Finite support translation geometry
-- statement:
--   Supporting lemmas analyze how translation-invariant finite supports contain successive orbit points. The bundle develops explicit distinctness and four-point enumeration arguments for a shift $\delta$, including points $a+k\delta$. These geometric facts support collision normal forms and quotient-orbit arguments without introducing a new stored structure.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/OrbitGeometry.lean; source file SHA-256 301a50141bf5b6aefa2b3cf86e410719029833feb8828428fb74641b35f89b27

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuotientOrbits_0c82b3d4a090

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem period_two_shape (a b c d δ : G) (hδ : δ ≠ 0) (h2 : δ+δ=0)
    (hba : b=a+δ) (hca : c ≠ a) (hcb : c ≠ b)
    (hc : ∀ x, (x=a ∨ x=b ∨ x=c ∨ x=d) →
      x+δ=a ∨ x+δ=b ∨ x+δ=c ∨ x+δ=d) : d=c+δ := by
  have hna : c+δ ≠ a := by
    intro h
    apply hcb
    calc c=(c+δ)+δ := by rw [add_assoc,h2,add_zero]
         _=b := by rw [h,hba]
  have hnb : c+δ ≠ b := by
    intro h
    apply hca
    exact add_right_cancel (h.trans hba)
  have hnc : c+δ ≠ c := by
    intro h
    apply hδ
    exact add_left_cancel (show c+δ=c+0 by simpa using h)
  exact (((hc c (by tauto)).resolve_left hna).resolve_left hnb).resolve_left hnc |>.symm

theorem period_four_shape (a b c d δ : G) (h4 : addOrderOf δ=4)
    (hba : b=a+δ)
    (hc : ∀ x, (x=a ∨ x=b ∨ x=c ∨ x=d) →
      x+δ=a ∨ x+δ=b ∨ x+δ=c ∨ x+δ=d) :
    (c=a+2 • δ ∧ d=a+3 • δ) ∨ (c=a+3 • δ ∧ d=a+2 • δ) := by
  let p : ℕ → G := fun k => a+k • δ
  have hi : ∀ i < 4, ∀ j < 4, p i=p j → i=j := by
    intro i hi j hj he
    apply nsmul_injOn_Iio_addOrderOf (x := δ)
      (by simpa only [Set.mem_Iio,h4] using hi) (by simpa only [Set.mem_Iio,h4] using hj)
    exact add_left_cancel he
  have hn : ∀ i < 4, ∀ j < 4, i ≠ j → p i ≠ p j := by
    intro i hi' j hj' hij he
    exact hij (hi i hi' j hj' he)
  have hp0 : p 0=a := by simp [p]
  have hp1 : p 1=b := by simp [p,hba]
  have h2a : p 2 ≠ a := by simpa only [← hp0] using hn 2 (by decide) 0 (by decide) (by decide)
  have h2b : p 2 ≠ b := by simpa only [← hp1] using hn 2 (by decide) 1 (by decide) (by decide)
  have h3a : p 3 ≠ a := by simpa only [← hp0] using hn 3 (by decide) 0 (by decide) (by decide)
  have h3b : p 3 ≠ b := by simpa only [← hp1] using hn 3 (by decide) 1 (by decide) (by decide)
  have h32 : p 3 ≠ p 2 := hn 3 (by decide) 2 (by decide) (by decide)
  have hb2 : b+δ=p 2 := by rw [hba]; simp [p,two_nsmul,add_assoc]
  have hp23 : p 2+δ=p 3 := by
    dsimp [p]
    rw [show (3 : ℕ)=2+1 from rfl,add_nsmul,one_nsmul]
    abel
  have hm2 : p 2=a ∨ p 2=b ∨ p 2=c ∨ p 2=d := by
    simpa only [hb2] using hc b (by tauto)
  have hm3 : p 3=a ∨ p 3=b ∨ p 3=c ∨ p 3=d := by
    simpa only [hp23] using hc (p 2) hm2
  rcases (hm2.resolve_left h2a).resolve_left h2b with hpc|hpd
  · have h3c : p 3 ≠ c := by simpa only [← hpc] using h32
    exact Or.inl ⟨hpc.symm,(((hm3.resolve_left h3a).resolve_left h3b).resolve_left h3c).symm⟩
  · have h3d : p 3 ≠ d := by simpa only [← hpd] using h32
    exact Or.inr ⟨(((hm3.resolve_left h3a).resolve_left h3b).resolve_right h3d).symm,hpd.symm⟩

end Couret.InterIA.Catalogue.Orbits


