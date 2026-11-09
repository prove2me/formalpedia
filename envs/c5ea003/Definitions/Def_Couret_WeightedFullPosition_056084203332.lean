-- Prove2me | Definitions.Def_Couret_WeightedFullPosition_056084203332
-- name    : Couret_WeightedFullPosition_056084203332
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:09:02.551176+00:00
-- url     : https://prove2.me/theorems/7a98c37b-5e5f-4043-8ddf-072ea44ef792
-- title:
--   Weighted three-position profiles and their unique partner
-- statement:
--   Defines the integral group-ring profile $\delta_i+\delta_j+2\delta_c$, and the partner position $c+(j-i)$ when $2(j-i)=0$, otherwise $i+j-c$. Bundled helper results derive translation invariance from equality of squared weighted profiles and prove uniqueness of the alternative position under the stated distinctness conditions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/WeightedFullPosition.lean; source file SHA-256 dd4284212807fae7b5a464f6a4836f0a20420be450257341cad34cea3ad4c439

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
import Definitions.Def_Couret_OrbitGeometry_a2664a5897aa

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo
open Couret.InterIA.Catalogue.Periods Couret.InterIA.Catalogue.Orbits
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The quotient occupation profile of two single sites and one full site. -/
noncomputable def weightedProfile (i j c : G) : AddMonoidAlgebra ℤ G :=
  atom i + atom j + 2*atom c

/-- Only the integer factor four is cancelled. -/
theorem weighted_square_invariant (i j c d : G)
    (hsq : weightedProfile i j c ^ 2 = weightedProfile i j d ^ 2) :
    atoms i j c d = atom (d-c) * atoms i j c d := by
  let W := atom i+atom j+atom c+atom d
  have h4 : (2 : AddMonoidAlgebra ℤ G)*(2*((atom c-atom d)*W))=0 := by
    calc _ = weightedProfile i j c ^ 2 - weightedProfile i j d ^ 2 := by
                dsimp [weightedProfile,W]; ring
         _ = 0 := by rw [hsq]; simp
  have hz := integer_coefficient_no_two_torsion _
    (integer_coefficient_no_two_torsion _ h4)
  have he : atom c*W=atom d*W := sub_eq_zero.mp (by simpa only [sub_mul] using hz)
  have ht := congrArg (fun f : AddMonoidAlgebra ℤ G => atom (-c)*f) he
  have hzero : atom (0 : G)=(1 : AddMonoidAlgebra ℤ G) := by
    simp [atom,AddMonoidAlgebra.one_def]
  simp only [← mul_assoc,atom_mul,neg_add_cancel,hzero,one_mul] at ht
  have hd : -c+d=d-c := by abel
  rw [hd] at ht
  simpa only [W,atoms,atom] using ht

/-- The unique possible different full-site position, when one exists. -/
def fullPartner (i j c : G) : G :=
  if (j-i)+(j-i)=0 then c+(j-i) else i+j-c

theorem invariant_full_position_partner (i j c d : G)
    (hdc : d ≠ c) (hic : i ≠ c) (hid : i ≠ d)
    (he : atoms i j c d=atom (d-c)*atoms i j c d) :
    d=fullPartner i j c := by
  let δ := d-c
  have hδ : δ ≠ 0 := sub_ne_zero.mpr hdc
  have hba : d=c+δ := by dsimp [δ]; abel
  have he' : atoms c d i j=atom δ*atoms c d i j := by
    simpa only [atoms,atom,add_assoc,add_comm,add_left_comm,δ] using he
  have hclose := atoms_translation_closed c d i j δ he'
  have hp : addOrderOf δ=2 ∨ addOrderOf δ=4 := by
    apply four_atoms_periods c d i j δ hδ
    simpa only [atoms,atom] using he'
  rcases hp with h2|h4
  · have hδ2 : δ+δ=0 := by
      simpa only [h2,two_nsmul] using addOrderOf_nsmul_eq_zero δ
    have hji := period_two_shape c d i j δ hδ hδ2 hba hic hid hclose
    have hdiff : j-i=δ := by rw [hji]; abel
    have htest : (j-i)+(j-i)=0 := by rw [hdiff]; exact hδ2
    simp only [fullPartner,htest,if_true]
    rw [hdiff]
    exact hba
  · have hδ4 : 4 • δ=0 := by simpa only [h4] using addOrderOf_nsmul_eq_zero δ
    have hδ2 : δ+δ ≠ 0 := by
      intro hz
      have hd : addOrderOf δ ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (by simpa only [two_nsmul] using hz)
      rw [h4] at hd
      norm_num at hd
    have shapes := period_four_shape c d i j δ h4 hba hclose
    have hex : (j-i=δ ∨ j-i= -δ) ∧ i+j-c=d := by
      rcases shapes with ⟨hi,hj⟩|⟨hi,hj⟩
      · constructor
        · left; rw [hi,hj]; simp only [succ_nsmul,zero_nsmul,zero_add]; abel
        · calc i+j-c = (c+δ)+4 • δ := by
                    rw [hi,hj]; simp only [succ_nsmul,zero_nsmul,zero_add]; abel
               _ = d := by rw [hδ4,add_zero]; exact hba.symm
      · constructor
        · right; rw [hi,hj]; simp only [succ_nsmul,zero_nsmul,zero_add]; abel
        · calc i+j-c = (c+δ)+4 • δ := by
                    rw [hi,hj]; simp only [succ_nsmul,zero_nsmul,zero_add]; abel
               _ = d := by rw [hδ4,add_zero]; exact hba.symm
    have htest : (j-i)+(j-i) ≠ 0 := by
      intro hz
      rcases hex.1 with hh|hh
      · rw [hh] at hz; exact hδ2 hz
      · rw [hh,← neg_add] at hz
        exact hδ2 (neg_eq_zero.mp hz)
    simp only [fullPartner,htest,if_false]
    exact hex.2.symm

/-- Universal uniqueness; the ambient abelian group need not be cyclic. -/
theorem weighted_full_position_unique (i j c d e : G)
    (hdc : d ≠ c) (hec : e ≠ c) (hic : i ≠ c)
    (hid : i ≠ d) (hie : i ≠ e)
    (hd : weightedProfile i j c ^ 2=weightedProfile i j d ^ 2)
    (he : weightedProfile i j c ^ 2=weightedProfile i j e ^ 2) : d=e := by
  exact (invariant_full_position_partner i j c d hdc hic hid
    (weighted_square_invariant i j c d hd)).trans
    (invariant_full_position_partner i j c e hec hic hie
      (weighted_square_invariant i j c e he)).symm

end Couret.InterIA.Fibres


