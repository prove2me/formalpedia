-- Prove2me | solution 1 for WeylHeisenbergSIC.exists_of_fiducial
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:06:11.754328+00:00
-- url     : https://prove2.me/submissions/61fd453c-af39-481a-b143-465f8bd3504e

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SICOrbitProof
variable {d : ℕ} [NeZero d]

private def orbit (ψ : ZMod d → ℂ) (q : ZMod d × ZMod d) (x : ZMod d) : ℂ :=
  ZMod.stdAddChar (q.2*x) * ψ (x+q.1)

private lemma character_normSq (x : ZMod d) : Complex.normSq (ZMod.stdAddChar x) = 1 := by
  rw [Complex.normSq_eq_norm_sq,AddChar.norm_apply,one_pow]

private lemma star_character (x : ZMod d) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change starRingEnd ℂ ((ZMod.toCircle x : Circle) : ℂ) = ((ZMod.toCircle (-x) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

private lemma orbit_normSq (ψ : ZMod d → ℂ) (q : ZMod d × ZMod d) :
    (∑ x : ZMod d, Complex.normSq (orbit ψ q x)) = ∑ x : ZMod d, Complex.normSq (ψ x) := by
  simp only [orbit,Complex.normSq_mul,character_normSq,one_mul]
  exact Equiv.sum_comp (Equiv.addRight q.1) (fun x => Complex.normSq (ψ x))

private lemma orbit_overlap (ψ : ZMod d → ℂ) (q r : ZMod d × ZMod d) :
    (∑ x : ZMod d, star (orbit ψ q x) * orbit ψ r x) =
      ZMod.stdAddChar ((q.2-r.2)*q.1) *
        ∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar ((r.2-q.2)*x) * ψ (x+(r.1-q.1))) := by
  calc
    _ = ∑ x : ZMod d, ZMod.stdAddChar ((r.2-q.2)*x) *
        star (ψ (x+q.1)) * ψ (x+r.1) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [orbit,star_mul,star_character]
      rw [show (r.2-q.2)*x = -(q.2*x)+r.2*x by ring,AddChar.map_add_eq_mul]
      ring
    _ = ∑ x : ZMod d, ZMod.stdAddChar ((r.2-q.2)*(x-q.1)) *
        star (ψ x) * ψ (x+(r.1-q.1)) := by
      apply Fintype.sum_equiv (Equiv.addRight q.1)
      intro x
      simp only [Equiv.coe_addRight,add_sub_cancel_right]
      rw [show x+q.1+(r.1-q.1) = x+r.1 by ring]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [show (r.2-q.2)*(x-q.1) = (q.2-r.2)*q.1+(r.2-q.2)*x by ring,
        AddChar.map_add_eq_mul]
      ring

end SICOrbitProof

open SICOrbitProof

/-- A single fiducial with constant nontrivial displacement overlaps generates a SIC. -/
theorem solution (d : ℕ) [NeZero d] (ψ : ZMod d → ℂ)
    (hnorm : (∑ x : ZMod d, Complex.normSq (ψ x)) = 1)
    (hfid : ∀ a b : ZMod d, (a,b) ≠ (0,0) →
      Complex.normSq (∑ x : ZMod d, star (ψ x) *
        (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹) :
    ∃ Φ : Fin (d^2) → EuclideanSpace ℂ (Fin d),
      (∀ i, ‖Φ i‖ = 1) ∧
      Pairwise (fun i j =>
        Complex.normSq (∑ k : Fin d, star (Φ i k) * Φ j k) = (d+1 : ℝ)⁻¹) := by
  classical
  let e : Fin (d^2) ≃ (ZMod d × ZMod d) :=
    Fintype.equivOfCardEq (by simp [pow_two])
  let c : Fin d ≃ ZMod d := (ZMod.finEquiv d).toEquiv
  let Φ (i : Fin (d^2)) : EuclideanSpace ℂ (Fin d) :=
    WithLp.toLp 2 (fun k => orbit ψ (e i) (c k))
  have hΦ (i : Fin (d^2)) (k : Fin d) : Φ i k = orbit ψ (e i) (c k) := rfl
  refine ⟨Φ,?_,?_⟩
  · intro i
    have hs : ‖Φ i‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [hΦ,← Complex.normSq_eq_norm_sq]
      rw [Equiv.sum_comp c (fun x => Complex.normSq (orbit ψ (e i) x)),orbit_normSq,hnorm]
    nlinarith [norm_nonneg (Φ i)]
  · intro i j hij
    have he : e i ≠ e j := fun h => hij (e.injective h)
    have hdisp : ((e j).1-(e i).1,(e j).2-(e i).2) ≠ (0,0) := by
      intro h
      apply he
      apply Prod.ext
      · exact (sub_eq_zero.mp (congrArg Prod.fst h)).symm
      · exact (sub_eq_zero.mp (congrArg Prod.snd h)).symm
    simp only [hΦ]
    rw [Equiv.sum_comp c (fun x => star (orbit ψ (e i) x) * orbit ψ (e j) x),
      orbit_overlap,Complex.normSq_mul,character_normSq,one_mul]
    exact hfid _ _ hdisp
