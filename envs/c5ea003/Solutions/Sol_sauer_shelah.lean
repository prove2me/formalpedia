-- Prove2me | solution 1 for sauer_shelah
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:34:52.057042+00:00
-- url     : https://prove2.me/submissions/58f09876-acad-46c6-8acc-0b48814fa90e

-- Sol generated from Algebra/SauerShelah.lean
import Mathlib
import Definitions.Def_Algebra_SauerShelah
import Theorems.Thm_card_le_one_of_vc_zero
import Theorems.Thm_card_split
import Theorems.Thm_shatters_embed_of_union
import Theorems.Thm_shatters_embed_union_last_of_inter

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/











-- ================================================================
--  Basic proj / embed API
-- ================================================================





/-- [Section: # CatalogBuild.Algebra.SauerShelah
Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17] -/
lemma last_not_mem_embed {n : ℕ} (T : Finset (Fin n)) :
    Fin.last n ∉ embed T := by
      simp +decide [ embed ]












lemma embed_card {n : ℕ} (T : Finset (Fin n)) : (embed T).card = T.card := by
  exact Finset.card_image_of_injective _ ( Fin.castSucc_injective _ )




lemma embed_union_last_card {n : ℕ} (T : Finset (Fin n)) :
    (embed T ∪ {Fin.last n}).card = T.card + 1 := by
      rw [ Finset.card_union, embed_card ] ; simp +decide [ last_not_mem_embed ]




























lemma binomial_pascal_sum (n d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), n.choose i) +
     ∑ i ∈ Finset.range d, n.choose i =
    ∑ i ∈ Finset.range (d + 1), (n + 1).choose i := by
      induction' d with d ih;
      · norm_num;
      · simp_all +arith +decide [ Nat.choose, Finset.sum_range_succ ]









theorem solution: ∀ (n d : ℕ) (F : Finset (Finset (Fin n))),
    (∀ A, Shatters F A → A.card ≤ d) →
    F.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i := by
  intro n; induction n with
  | zero =>
    intro d F hF
    fin_cases F <;> simp +arith +decide [ Finset.sum_range_succ' ]
  | succ n ih =>
    intro d F hF
    cases d with
    | zero =>
      have h := card_le_one_of_vc_zero F hF
      simp; omega
    | succ d =>
      set F₀ := (F.filter (Fin.last n ∉ ·)).image proj
      set F₁ := (F.filter (Fin.last n ∈ ·)).image proj
      have hsplit := card_split F
      have hvc₀ : ∀ A, Shatters (F₀ ∪ F₁) A → A.card ≤ d + 1 := fun A hA => by
        have := hF _ (shatters_embed_of_union F hA); rwa [embed_card] at this
      have hvc₁ : ∀ A, Shatters (F₀ ∩ F₁) A → A.card ≤ d := fun A hA => by
        have := hF _ (shatters_embed_union_last_of_inter F hA)
        rw [embed_union_last_card] at this; omega
      have h_union := ih (d + 1) (F₀ ∪ F₁) hvc₀
      have h_inter := ih d (F₀ ∩ F₁) hvc₁
      have hpascal := binomial_pascal_sum n (d + 1)
      linarith
