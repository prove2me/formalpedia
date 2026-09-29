-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_uniform_common_prime
-- name    : mme_dwz_table2_claim6_8_uniform_common_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:56:20.799785+00:00
-- url     : https://prove2.me/theorems/59ee3ea2-30e6-4e26-a81c-bc6d4553dfda
-- title:
--   One common Claim-6.8 prime for all Table-2 candidate fibers
-- statement:
--   For a Table-2 multiplier m and first-hash degree d, form the compatible outer-candidate set C(I,s) for every retained outer word I and typical small word s. There are integers D and p such that every |C(I,s)|≤D, the maximum D obeys the explicit entropy-rate bound R, and one odd prime p simultaneously satisfies 8d≤p and 8|C(I,s)|≤p for every pair. Moreover p lies above max(4,8 max(d,D)), at most twice that threshold, and p≤max(8,16 max(d,R)) over the reals. The modulus is therefore chosen before, and shared by, every retained/typical pair.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Equation (21), Claim 6.8, and Section 6.

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_claim6_8_uniform_common_prime
    (m d : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let regionOfShape :
          Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
        if h : MME.DWZSquare.shapeX s = 0 ∨
            MME.DWZSquare.shapeY s = 0 then
          Sum.inl ⟨s, h⟩
        else
          Sum.inr (MME.DWZSquare.shapeZ s)
      let Outer :=
        {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t // w t = s} =
            MME.DWZTable2Counts.component s * m}
      let Typical :=
        {small : Fin (MME.DWZTable2Counts.scale * m) → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ q, Fintype.card {t // small t = q} =
            MME.DWZTable2Counts.gamma q * m}
      let Compatible : Outer → Typical → Prop := fun I small ↦
        ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
          Fintype.card
              {t //
                regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
            MME.DWZTable2Cardinality.cellCount m r a
      let candidates : Outer → Typical → Finset Outer := fun retained small ↦
        Finset.univ.filter
          (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
      let R : ℝ :=
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      (∀ k, Fintype.card {t // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧ Nonempty Typical ∧
        ∃ D p : ℕ,
          (∀ retained small, (candidates retained small).card ≤ D) ∧
          (D : ℝ) ≤ R ∧
          p.Prime ∧ Odd p ∧ 4 < p ∧
          8 * d ≤ p ∧
          (∀ retained small,
            8 * (candidates retained small).card ≤ p) ∧
          max 4 (8 * max d D) < p ∧
          p ≤ 2 * max 4 (8 * max d D) ∧
          (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
  sorry
