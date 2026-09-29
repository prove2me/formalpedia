-- Prove2me | solution 1 for shatters_embed_union_last_of_inter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:44.475767+00:00
-- url     : https://prove2.me/submissions/2527a48b-3748-4b53-a7e4-2aa6e7163771

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

























































theorem solution{n : ℕ} (F : Finset (Finset (Fin (n + 1))))
    {A : Finset (Fin n)}
    (h : Shatters ((F.filter (Fin.last n ∉ ·)).image proj ∩
                    (F.filter (Fin.last n ∈ ·)).image proj) A) :
    Shatters F (embed A ∪ {Fin.last n}) := by
      -- Let B be a subset of embed A ∪ {last n}. We need to find S ∈ F such that (embed A ∪ {last n}) ∩ S = B.
      intro B hB
      by_cases h_last : Fin.last n ∈ B;
      · obtain ⟨T, hT⟩ : ∃ T ∈ (F.filter (Fin.last n∉ ·)).image proj ∩ (F.filter (Fin.last n ∈ ·)).image proj, A ∩ T = proj B := by
          apply h;
          intro i hi; specialize hB ( show Fin.castSucc i ∈ B from ?_ ) ; aesop;
          unfold embed at hB; aesop;
        obtain ⟨S₁, hS₁⟩ : ∃ S₁ ∈ F, Fin.last n∉ S₁ ∧ proj S₁ = T := by
          aesop
        obtain ⟨S₂, hS₂⟩ : ∃ S₂ ∈ F, Fin.last n ∈ S₂ ∧ proj S₂ = T := by
          aesop;
        use S₂; simp_all +decide [ Finset.ext_iff ] ;
        intro a; specialize hB; have := @hB a; simp_all +decide [ Finset.subset_iff ] ;
        cases a using Fin.lastCases <;> simp_all +decide [ embed ];
      · -- Since $last n \notin B$, we have $B \subseteq embed A$.
        have hB_subset : B ⊆ embed A := by
          intro x hx; specialize hB hx; aesop;
        -- Since $B \subseteq embed A$, there exists $T \in F₀ \cap F₁$ such that $A \cap T = proj B$.
        obtain ⟨T, hT⟩ : ∃ T ∈ (F.filter (Fin.last n∉·)).image proj ∩ (F.filter (Fin.last n ∈ ·)).image proj, A ∩ T = proj B := by
          apply h (proj B) (by
          simp_all +decide [ Finset.subset_iff ];
          intro x hx; specialize hB_subset hx; unfold embed at hB_subset; aesop;);
        obtain ⟨S₀, hS₀⟩ : ∃ S₀ ∈ F, Fin.last n∉S₀ ∧ proj S₀ = T := by
          aesop
        obtain ⟨S₁, hS₁⟩ : ∃ S₁ ∈ F, Fin.last n ∈ S₁ ∧ proj S₁ = T := by
          aesop;
        use S₀;
        simp_all +decide [ Finset.ext_iff ];
        intro a; induction a using Fin.lastCases <;> simp_all +decide [ embed ] ;
