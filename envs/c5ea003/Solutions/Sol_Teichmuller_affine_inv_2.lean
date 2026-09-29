-- Prove2me | solution 2 for Teichmuller.affine_inv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:57:52.729469+00:00
-- url     : https://prove2.me/submissions/a0f2ffcc-02a2-4693-901a-44b69738895d

import Definitions.Def_Geometry_Teichmuller_TorusSpace
open Teichmuller Complex UpperHalfPlane in
theorem solution (τ τ' : ℍ) : (affine τ τ').inv = affine τ' τ := by
  have hy := τ.im_pos
  have hy' := τ'.im_pos
  have hj : (affine τ τ').jac = τ'.im / τ.im := by
    simp only [LinMap.jac, affine, norm_div, div_pow]
    rw [normSq_sub_cbar τ τ', norm_sub_cbar_self, norm_sub_rev (τ : ℂ) (τ' : ℂ)]
    field_simp
    ring
  suffices H : ∀ f g : LinMap, f.a = g.a → f.b = g.b → f = g by
    apply H
    · show (starRingEnd ℂ) (affine τ τ').a / ((affine τ τ').jac : ℂ) = (affine τ' τ).a
      rw [hj]
      simp only [affine, cbar]
      apply Complex.ext <;>
        simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> field_simp <;> ring
    · show -(affine τ τ').b / ((affine τ τ').jac : ℂ) = (affine τ' τ).b
      rw [hj]
      simp only [affine, cbar]
      apply Complex.ext <;>
        simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> field_simp <;> ring
  rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h1 h2
  simp only at h1 h2
  subst h1; subst h2; rfl
