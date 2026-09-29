-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_uniform_common_prime_with_card_cap
-- name    : mme_dwz_table2_claim6_8_uniform_common_prime_with_card_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:07:21.577383+00:00
-- url     : https://prove2.me/theorems/eb1733d7-90b7-4646-aaef-5a2be22ad838
-- title:
--   Uniform Claim-6.8 prime with an outer-family cardinal cap
-- statement:
--   For the integral Table-2 parameters and any first-hash degree $d$, choose a prescribed coarse-Z word and consider all exact outer words and typical fine words above it. There are integers $Q,p$ such that every compatible-candidate family has size at most $Q$, the cap satisfies $Q\leq|\mathrm{Outer}|$, and one prime $p$ simultaneously satisfies the first-hash bound $8d\leq p$, every Claim-6.8 bound $8|\mathrm{candidates}|\leq p$, the standard Bertrand upper bound, and the entropy-compatible real upper bound. The explicit inequality $Q\leq|\mathrm{Outer}|$ connects the finite prime witness to the later elementary bound $Q\leq15^L$.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21) and Claim 6.8; finite common-prime specialization.

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap

open scoped BigOperators

set_option autoImplicit false

/-- Table-2 specialization of the common-prime choice which additionally
records that its second-hash collision cap `Q` is no larger than the literal
fixed-coarse-word outer family. -/

theorem mme_dwz_table2_claim6_8_uniform_common_prime_with_card_cap
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
        ∃ Q p : ℕ,
          (∀ retained small, (candidates retained small).card ≤ Q) ∧
          Q ≤ Nat.card Outer ∧
          (Q : ℝ) ≤ R ∧
          p.Prime ∧ Odd p ∧ 4 < p ∧
          8 * d ≤ p ∧
          (∀ retained small,
            8 * (candidates retained small).card ≤ p) ∧
          max 4 (8 * max d Q) < p ∧
          p ≤ 2 * max 4 (8 * max d Q) ∧
          (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R)  := by
  sorry
