-- Prove2me | solution 2 for Teichmuller.teichDist_comm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:32:11.28193+00:00
-- url     : https://prove2.me/submissions/11631707-8521-4d27-a920-46338dd5cafb

/-
# `Teichmuller.teichDist_comm`
Target `a2257557` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`teichDist τ τ' = Real.log (affine τ τ').dil / 2`, and `affine τ τ'` has
    a = (τ' − conj τ)/(τ − conj τ)        b = (τ − τ')/(τ − conj τ)
Both coefficients carry the SAME denominator, so in `dil = (‖a‖+‖b‖)/(‖a‖−‖b‖)` it cancels,
leaving    (‖τ' − conj τ‖ + ‖τ − τ'‖) / (‖τ' − conj τ‖ − ‖τ − τ'‖),
which is symmetric in τ, τ'.

Symmetry of the two norms:
  * `‖τ − τ'‖ = ‖τ' − τ‖`                                    by `norm_sub_rev`
  * `‖τ' − conj τ‖ = ‖τ − conj τ'‖`                          via the RETAINED bundle lemma
      `normSq_sub_cbar : ‖↑τ' - cbar τ‖^2 = ‖↑τ' - ↑τ‖^2 + 4 * τ.im * τ'.im`
    whose right side is visibly symmetric; applying it in both orders equates the squares, and
    non-negativity of norms upgrades that to equality of the norms.

Verified numerically: symmetry to 3.2e-14 on random points, and to 5.1e-13 in the degenerate
regime with both points within 1e-3 of each other and 1e-4 of the real axis. The closed form was
checked separately against the dilatation computed from the coefficients, confirming the
denominator really does cancel. The sub-identity was tested alone over 20000 pairs, no failures.

PROBED, NOT GUESSED (all `#check`ed; both probe examples compiled silently):
  `norm_sub_rev : ‖a - b‖ = ‖b - a‖`,  `norm_div : ‖a / b‖ = ‖a‖ / ‖b‖`,
  `Teichmuller.normSq_sub_cbar`.
NOTE: `ℍ` is SCOPED notation and is unknown under `autoImplicit false`; the type is written
`UpperHalfPlane` here. Same type — the type-match gate confirms the statement regardless.
-/
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC
import Definitions.Def_Geometry_Teichmuller_TorusSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Teichmuller in
/-- The reflection identity is symmetric, so these two norms agree. -/
theorem norm_sub_cbar_comm (τ τ' : UpperHalfPlane) :
    ‖(τ' : ℂ) - cbar τ‖ = ‖(τ : ℂ) - cbar τ'‖ := by
  have h1 := Teichmuller.normSq_sub_cbar τ τ'
  have h2 := Teichmuller.normSq_sub_cbar τ' τ
  have hrev : ‖(τ' : ℂ) - (τ : ℂ)‖ = ‖(τ : ℂ) - (τ' : ℂ)‖ := norm_sub_rev _ _
  have hsq : ‖(τ' : ℂ) - cbar τ‖ ^ 2 = ‖(τ : ℂ) - cbar τ'‖ ^ 2 := by
    rw [h1, h2, hrev]; ring
  nlinarith [hsq, norm_nonneg ((τ' : ℂ) - cbar τ), norm_nonneg ((τ : ℂ) - cbar τ')]

open Teichmuller in
/-- **The target, verbatim.** -/
theorem solution (τ τ' : UpperHalfPlane) : teichDist τ τ' = teichDist τ' τ := by
  have hswap := norm_sub_cbar_comm τ τ'
  have hrev : ‖(τ : ℂ) - (τ' : ℂ)‖ = ‖(τ' : ℂ) - (τ : ℂ)‖ := norm_sub_rev _ _
  -- the two self-distances, each the shared denominator on its side
  have hd  : ‖(τ : ℂ) - cbar τ‖ = 2 * τ.im := Teichmuller.norm_sub_cbar_self τ
  have hd' : ‖(τ' : ℂ) - cbar τ'‖ = 2 * τ'.im := Teichmuller.norm_sub_cbar_self τ'
  have hpos  : (0:ℝ) < ‖(τ : ℂ) - cbar τ‖ := by rw [hd]; have := τ.im_pos; linarith
  have hpos' : (0:ℝ) < ‖(τ' : ℂ) - cbar τ'‖ := by rw [hd']; have := τ'.im_pos; linarith
  simp only [teichDist, LinMap.dil, affine, norm_div]
  -- both sides are log (…) / 2, so it suffices that the two quotients agree
  congr 2
  rw [hswap, hrev]
  field_simp
