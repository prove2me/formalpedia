-- Prove2me | solution 1 for shatters_embed_of_union
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:43.904651+00:00
-- url     : https://prove2.me/submissions/4d26629b-9759-47bc-8986-c0db52660fdf

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

























lemma embed_inter_eq {n : ℕ} (A : Finset (Fin n)) (S : Finset (Fin (n + 1))) :
    embed A ∩ S = embed (A ∩ proj S) := by
      ext x; simp [embed, proj] ;
      grind +ring




lemma eq_embed_proj_of_last_not_mem {n : ℕ} {S : Finset (Fin (n + 1))}
    (h : Fin.last n ∉ S) : S = embed (proj S) := by
      -- By definition of $proj$ and $embed$, we know that $x \in S$ if and only if $x \in embed (proj S)$.
      ext x; simp [embed, proj];
      cases x using Fin.lastCases <;> aesop





























theorem solution{n : ℕ} (F : Finset (Finset (Fin (n + 1))))
    {A : Finset (Fin n)}
    (h : Shatters ((F.filter (Fin.last n ∉ ·)).image proj ∪
                    (F.filter (Fin.last n ∈ ·)).image proj) A) :
    Shatters F (embed A) := by
      intro B hB
      obtain ⟨T, hT⟩ : ∃ T ∈ Finset.image proj ({x ∈ F | last n ∉ x}) ∪ Finset.image proj ({x ∈ F | last n ∈ x}), A ∩ T = proj B := by
        exact h _ ( Finset.subset_iff.mpr fun i hi => by
          simp_all +decide [ Finset.subset_iff, proj, embed ];
          cases hB hi ; aesop );
      obtain ⟨S, hS⟩ : ∃ S ∈ F, T = proj S := by
        aesop;
      use S, hS.left;
      have h_eq : B = embed (proj B) := by
        apply eq_embed_proj_of_last_not_mem;
        intro h_last_in_B; have := hB h_last_in_B; simp_all +decide [ embed ] ;
      convert embed_inter_eq A S using 1;
      simpa only [ ← hS.2, hT.2 ] using h_eq
