-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_bounded_address_adapter
-- name    : mme_dwz_table2_claim6_8_bounded_address_adapter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:06:23.366956+00:00
-- url     : https://prove2.me/theorems/c587adff-58be-4b30-a241-aba8dde660f9
-- title:
--   DWZ Table 2 Claim 6.8: positive-length bounded-address adapter
-- statement:
--   At positive Table-2 multiplier m, reindex the exact source position type Fin(10^16 m) as Fin(n+1), where n=10^16 m-1. For a fixed coarse Z word K, let Outer be the literal family of all exact Table-2 component words over K, let Typical be the literal fine-pair words with exact gamma histogram, and impose the exact boundary/interior compatibility conditions preceding Equation (23). Pull each outer X address and K through the reindexing into the bounded alphabet Fin 5. For any retained outer word and typical small word, if every actual bad (hole) hash parameter has a distinct compatible outer witness colliding with the conditioned retained Z hash, and if the odd prime modulus is at least eight times the number of such candidates, then at most one eighth of all conditioned weight assignments are bad. The proof must establish the positive-length predecessor identity and injectivity of the reindexed shapeX address from the concrete Table-2 rows, rather than assuming modular address distinctness.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Definitions 6.4 and 6.6, Lemma 6.7, Claim 6.8, Equations (22)-(23), printed pp. 54-57 (PDF pp. 55-58), together with Table 2 on printed p. 59 (PDF p. 60).

import Theorems.Thm_mme_dwz_claim6_8_outer_candidates_survive
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_claim6_8_bounded_address_adapter
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : 4 < p) (b0 : ZMod p) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let n := sourceLength - 1
    let reindex : Fin (n + 1) ≃ Fin sourceLength :=
      finCongr (by
        dsimp only [n, sourceLength]
        exact Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Fin sourceLength → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Fin sourceLength // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Fin sourceLength → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ q, Fintype.card {t : Fin sourceLength // small t = q} =
          MME.DWZTable2Counts.gamma q * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Fin sourceLength //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
      MME.DWZSquare.shapeX (I.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
    ∀ (retained : Outer) (small : Typical)
      (bad : (Fin (n + 1) → ZMod p) → Prop) [DecidablePred bad],
      let outerCandidates :=
        Finset.univ.filter
          (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
      let hX : (Fin (n + 1) → ZMod p) →
          (Fin (n + 1) → Fin 5) → ZMod p :=
        fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
      let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
          (Fin (n + 1) → Fin 5) → ZMod p :=
        fun w0 w C ↦
          b0 + (2 : ZMod p)⁻¹ *
            (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
      let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
        fun w ↦
          2 * (∑ t, ((addressX retained t).val : ZMod p) * w t) -
            ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
      (∀ w, bad w →
        ∃ A ∈ outerCandidates,
          hX w (addressX A) = hZ (conditionedW0 w) w addressZ) →
      8 * outerCandidates.card ≤ p →
      8 * (Finset.univ.filter bad).card ≤
        Fintype.card (Fin (n + 1) → ZMod p) := by sorry
