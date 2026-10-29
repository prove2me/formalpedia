-- Prove2me | solution 1 for MovingSofa.canonical_paper_motion_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:35:19.350023+00:00
-- url     : https://prove2.me/submissions/76809142-5093-45cf-8166-b66604fd4865

import Mathlib
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Motion_Paper
import Theorems.Thm_MovingSofa_IsMovingSofa_isPaperMotion
open Set MeasureTheory
open scoped unitInterval

open MovingSofa in
theorem solution :
    (∀ s : Set Point, IsPaperMovingSofa s →
      ∃ (q : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
        IsMovingSofa ((fun p ↦ p + q) '' s) m ∧
        volume ((fun p ↦ p + q) '' s) = volume s) ∧
    (∀ (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
      IsMovingSofa s m → IsPaperMovingSofa s) := by
  refine ⟨?_, fun s m h => ⟨m, h.isPaperMotion⟩⟩
  rintro s ⟨m, hconn, hclosed, hcont, ⟨q, hq⟩, -, hinit, hhall, hfinal⟩
  let e : Point ≃ᵃⁱ[ℝ] Point := AffineIsometryEquiv.constVAdd ℝ Point (-q)
  have he : ∀ p, e p = -q + p := fun p => rfl
  refine ⟨q, fun t => e.trans (m t), ?_, ?_⟩
  · have himg : ∀ t, (e.trans (m t)) '' ((fun p ↦ p + q) '' s) = m t '' s := by
      intro t
      rw [image_image]
      congr 1
      funext p
      simp [AffineIsometryEquiv.coe_trans, he]
    have hs0 : (fun p ↦ p + q) '' s = m 0 '' s := by
      congr 1; funext p; exact (hq p).symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hconn.image _ (continuous_add_right q).continuousOn
    · exact (Homeomorph.addRight q).isClosedMap s hclosed
    · apply continuous_induced_rng.2
      have h1 : Continuous fun t : I =>
          (m t).toAffineIsometry.toContinuousAffineMap.toContinuousMap :=
        continuous_induced_dom.comp hcont
      refine ((ContinuousMap.continuous_precomp
        e.toAffineIsometry.toContinuousAffineMap.toContinuousMap).comp h1).congr ?_
      intro t
      ext p
      rfl
    · ext p
      simp [AffineIsometryEquiv.coe_trans, he, hq]
    · rw [hs0]; exact hinit
    · intro t; rw [himg]; exact hhall t
    · rw [himg]; exact hfinal
  · rw [image_add_right]
    exact measure_preimage_add_right volume (-q) s
