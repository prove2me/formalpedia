-- Prove2me | Theorems.Thm_mme_dwz_table2_global_exact_profile_common_prime
-- name    : mme_dwz_table2_global_exact_profile_common_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:26:01.431065+00:00
-- url     : https://prove2.me/theorems/a642dcc9-7fac-47b2-84d8-24389612348e
-- title:
--   One Claim-6.8 prime controls the full exact-profile Table-2 family
-- statement:
--   Let $L$ be the scaled Table-2 length, and let $T$ be the full family of words with the prescribed fifteen-component histogram. For every retained owner $u\in T$ and every useful fine block $z$ over $u$, let $C(u,z)$ be the exact-profile competitors which share $u$'s complete coarse-$Z$ word and satisfy the retained fine compatibility equations. If $d\le 15^L$, then there is one odd prime $p$ and one collision cap $Q$ controlling all these families simultaneously:
--
--   $$|C(u,z)|\le Q,\qquad 8|C(u,z)|\le p,\qquad 8d\le p,$$
--
--   with $Q\le15^L$ and $p\le\exp(16(L+1))$. Moreover, $Q$ is bounded by the sharp Claim-6.8 rate formed with a single reference fixed-coarse-$Z$ fiber. This preserves the compatibility-rate factor while making the second hash common across the entire exact-profile family.
-- source:
--   Duan--Wu--Zhou Claim 6.8, combined with exact Table-2 profile transport and uniform finite-family prime selection.

import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts
import Theorems.Thm_mme_dwz_global_exact_profile_competitor_card_upper
import Theorems.Thm_mme_dwz_table2_outer_equiv_across_coarse_Z_words
import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Theorems.Thm_mme_dwz_common_prime_le_exp_sixteen_length

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_global_exact_profile_common_prime
    (m d : ℕ) (hd : d ≤ 15 ^ (MME.DWZTable2Counts.scale * m)) :
    let L := MME.DWZTable2Counts.scale * m
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let Owner := {w : Fin L → Fin 15 // ExactProfile w}
    ∃ base : Owner,
      let K₀ : Fin L → Fin 5 := fun t ↦
        MME.DWZSquare.shapeZ (base.1 t)
      let FixedOuter₀ :=
        {w : Fin L → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K₀ t) ∧ ExactProfile w}
      let R : ℝ :=
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card FixedOuter₀ : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      let candidate : ∀ retained : Owner,
          MME.DWZTable2StandardForm.UsefulBlock m retained.1 →
            Finset (Fin L → Fin 15) := fun retained small ↦ by
        classical
        exact T.filter (fun w ↦
          (∀ t, MME.DWZSquare.shapeZ (w t) =
            MME.DWZSquare.shapeZ (retained.1 t)) ∧
          MME.DWZStep2Source.retainedFineCompatible m
            (fun w : Fin L → Fin 15 ↦ w)
            (fun t ↦ MME.DWZStep1Support.fineSplitGrade
              (small.1 t).1 (small.1 t).2) w)
      ∃ Q p : ℕ,
        (∀ retained small, (candidate retained small).card ≤ Q) ∧
        Q ≤ 15 ^ L ∧
        (Q : ℝ) ≤ R ∧
        p.Prime ∧ Odd p ∧ 4 < p ∧
        8 * d ≤ p ∧
        (∀ retained small, 8 * (candidate retained small).card ≤ p) ∧
        max 4 (8 * max d Q) < p ∧
        p ≤ 2 * max 4 (8 * max d Q) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
  sorry
