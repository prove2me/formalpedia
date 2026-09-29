-- Prove2me | solution 1 for card_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:41.173085+00:00
-- url     : https://prove2.me/submissions/717f9ae5-052b-480a-b2bd-3d7c96215861

-- Sol generated from Algebra/SauerShelah.lean
import Mathlib
import Definitions.Def_Algebra_SauerShelah

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/











-- ================================================================
--  Basic proj / embed API
-- ================================================================

@[simp] lemma mem_proj {n : ℕ} {S : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ proj S ↔ i.castSucc ∈ S := by simp [proj]

























































theorem solution{n : ℕ} (F : Finset (Finset (Fin (n + 1)))) :
    F.card = ((F.filter (Fin.last n ∉ ·)).image proj ∪
              (F.filter (Fin.last n ∈ ·)).image proj).card +
             ((F.filter (Fin.last n ∉ ·)).image proj ∩
              (F.filter (Fin.last n ∈ ·)).image proj).card := by
                -- By definition of $F₀$ and $F₁$, we have $F = F₀ ∪ F₁$.
                have h_union : F = Finset.filter (Fin.last n∉·) F ∪ Finset.filter (Fin.last n∈·) F := by
                  grind +ring;
                -- By definition of $F₀$ and $F₁$, we have $|F₀| = |\text{proj}(F₀)|$ and $|F₁| = |\text{proj}(F₁)|$.
                have h_card_F₀ : (Finset.filter (Fin.last n∉·) F).card = (Finset.image proj (Finset.filter (Fin.last n∉·) F)).card := by
                  rw [ Finset.card_image_of_injOn ];
                  intro x hx y hy; simp +decide [ Finset.ext_iff ] at *;
                  intro h a; induction a using Fin.lastCases <;> simp_all +singlePass ;
                have h_card_F₁ : (Finset.filter (Fin.last n∈·) F).card = (Finset.image proj (Finset.filter (Fin.last n∈·) F)).card := by
                  rw [ Finset.card_image_of_injOn ];
                  intro x hx y hy; simp +decide [ Finset.ext_iff ] at *;
                  intro h a; induction a using Fin.lastCases <;> simp +decide [ * ] ;
                conv_lhs => rw [ h_union ];
                rw [ Finset.card_union_add_card_inter ];
                rw [ ← h_card_F₀, ← h_card_F₁, Finset.card_union_of_disjoint ] ; exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
