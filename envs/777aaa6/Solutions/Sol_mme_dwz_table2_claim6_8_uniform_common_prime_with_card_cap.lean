-- Prove2me | solution 1 for mme_dwz_table2_claim6_8_uniform_common_prime_with_card_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:09:18.973056+00:00
-- url     : https://prove2.me/submissions/2ce26c51-c169-4f77-9f36-bf054820c84d

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- Table-2 specialization of the common-prime choice which additionally
records that its second-hash collision cap `Q` is no larger than the literal
fixed-coarse-word outer family. -/
theorem solution
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
          (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
  classical
  obtain ⟨K, hK, hOuter, hTypical, _hInjective, _hFactor, hprime⟩ :=
    mme_dwz_table2_compatible_outer_candidate_prime_budget m
  refine ⟨K, ?_⟩
  dsimp only
  refine ⟨hK, hOuter, hTypical, ?_⟩
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
          {t : Fin (MME.DWZTable2Counts.scale * m) //
            (if h : MME.DWZSquare.shapeX (I.1 t) = 0 ∨
                MME.DWZSquare.shapeY (I.1 t) = 0 then
              Sum.inl ⟨I.1 t, h⟩
            else
              Sum.inr (MME.DWZSquare.shapeZ (I.1 t))) = r ∧
              (small.1 t).1 = a} =
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
  have hR : ∀ retained small,
      ((candidates retained small).card : ℝ) ≤ R := by
    intro retained small
    obtain ⟨c, hc, hcR, _p, _hp, _hpodd, _h4p, _hbudget,
      _hlower, _hupper, _hpRate⟩ := hprime retained small
    have hcEq : c = candidates retained small := by
      ext A
      simpa only [candidates, Compatible, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc A
    rw [← hcEq]
    exact hcR
  letI : Nonempty Outer := hOuter
  letI : Nonempty Typical := hTypical
  have hcommon :=
    mme_dwz_finite_candidate_family_common_prime_with_card_cap
      candidates d R hR
  simpa only [Outer, Typical, Compatible, candidates, R,
    Nat.card_eq_fintype_card] using hcommon
