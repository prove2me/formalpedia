-- Prove2me | Theorems.Thm_mme_dwz_global_exact_profile_competitor_card_upper
-- name    : mme_dwz_global_exact_profile_competitor_card_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:48:04.070413+00:00
-- url     : https://prove2.me/theorems/865ffa5f-e6aa-4778-9878-d0170dc1619c
-- title:
--   Full-profile Claim-6.8 competitors embed into the owner's fixed-Z fiber
-- statement:
--   Fix a Table-2 scale $m$ and a finite family $T$ of component words, each having the prescribed exact fifteen-cell profile. Let $I$ be one retained word, let $K$ be its coordinatewise coarse $Z$ word, and let $z$ be one useful fine $Z$ word above $I$. Among the words of $T$, retain those that have the same complete coarse $Z$ word as $I$ and satisfy the fine regional split constraints determined by $z$. If $\mathcal O_K$ is the full exact-profile outer family above $K$, then the number of such competitors is at most
--
--   $$
--   (6(L+1))^9 |\mathcal O_K| \exp\left(mL_0\log 2\cdot\log\alpha_P\right).
--   $$
--
--   Here $L_0$ is the fixed Table-2 scale and $L=L_0m$. This is the uniform owner-by-owner form of the Equation-(22) candidate bound needed to choose one Claim-6.8 prime across the full exact-profile first-hash target, rather than only inside one preselected coarse-$Z$ fiber.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (22) and Claim 6.8, printed pp. 56--57 (PDF pp. 57--58), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_count_upper
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
import Mathlib.Data.Finite.Card

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_global_exact_profile_competitor_card_upper
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (T : Finset (Position → Fin 15))
    (hTExact : ∀ w ∈ T, ∀ s,
      Fintype.card {t : Position // w t = s} =
        MME.DWZTable2Counts.component s * m)
    (retained : Position → Fin 15)
    (hK : ∀ k,
      Fintype.card
          {t : Position // MME.DWZSquare.shapeZ (retained t) = k} =
        MME.DWZTable2Counts.alphaZ k * m)
    (small : MME.DWZTable2StandardForm.UsefulBlock m retained) :
    let K : Position → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained t)
    let Outer :=
      {w : Position → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Position // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let candidate : (Position → Fin 15) → Prop := fun w ↦
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Position → Fin 15 ↦ w)
        (fun t ↦ MME.DWZStep1Support.fineSplitGrade
          (small.1 t).1 (small.1 t).2) w
    let candidates : Finset (Position → Fin 15) := by
      classical
      exact T.filter candidate
    ((candidates.card : ℕ) : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.card Outer : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP) := by
  sorry
