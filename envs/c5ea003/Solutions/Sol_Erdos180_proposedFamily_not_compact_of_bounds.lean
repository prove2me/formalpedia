-- Prove2me | solution 1 for Erdos180.proposedFamily_not_compact_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:55:30.697087+00:00
-- url     : https://prove2.me/submissions/725a9e8a-db06-490f-bdff-4fe93cf8a9f3

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Theorems.Thm_Erdos180_manuscriptLowerConstant_pos

namespace Erdos180

noncomputable section
open Filter Finset SimpleGraph
open scoped Topology

lemma extremalScale_pos {n : ℕ} (hn : 0 < n) :
    0 < extremalScale n := by
  unfold extremalScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma not_compact_of_separation
    {family : Finset FiniteGraph}
    (certificate : SeparationCertificate family) :
    ¬ IsCompactFamily family := by
  rintro ⟨forbidden, hmem, C, hC, hcomparison⟩
  have hepsilon : 0 < certificate.lowerConstant / (2 * C) := by
    exact div_pos certificate.lowerConstant_pos
      (mul_pos (by norm_num) hC)
  have hupper := certificate.family_littleO
    (certificate.lowerConstant / (2 * C)) hepsilon
  have hlower := certificate.member_lower forbidden hmem
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  have himpossible : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hupper, hlower, hcomparison, hpositive]
      with n hnupper hnlower hncomparison hnpositive
    have hs := extremalScale_pos hnpositive
    have hscaled :
        C * (familyExtremal family n : ℝ) ≤
          C * ((certificate.lowerConstant / (2 * C)) *
            extremalScale n) :=
      mul_le_mul_of_nonneg_left hnupper hC.le
    have hidentity :
        C * ((certificate.lowerConstant / (2 * C)) *
          extremalScale n) =
            (certificate.lowerConstant / 2) * extremalScale n := by
      field_simp
    rw [hidentity] at hscaled
    nlinarith [mul_pos certificate.lowerConstant_pos hs]
  exact himpossible.exists.elim (fun _ h => h)

end

end Erdos180

open Erdos180
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ IsCompactFamily proposedFamily := by
  apply not_compact_of_separation
  exact
    { lowerConstant := manuscriptLowerConstant
      lowerConstant_pos := manuscriptLowerConstant_pos
      family_littleO := hupper
      member_lower := hlower }
