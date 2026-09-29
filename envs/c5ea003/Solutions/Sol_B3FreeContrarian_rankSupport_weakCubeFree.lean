-- Prove2me | solution 1 for B3FreeContrarian.rankSupport_weakCubeFree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:46:50.775186+00:00
-- url     : https://prove2.me/submissions/00b30147-f0ea-406a-a83d-c92752d3e2d7

-- Sol generated from Probability/B3FreeContrarian.lean
import Mathlib
import Definitions.Def_Probability_B3FreeContrarian

/-!
# Contrarian tests around weak and strong Boolean-cube avoidance

This file formalizes two general obstructions to a weak copy of the Boolean lattice
`B_d`, and an explicit strong-copy construction.  The rank-support theorem strengthens
the usual consecutive-layer argument: the occupied ranks need not be consecutive.
The small-family theorem gives a different obstruction and disproves the tempting
claim that merely meeting `d+1` ranks forces a copy of `B_d`.
-/

open Finset
open scoped Classical

open B3FreeContrarian





/-
Every strong copy is weak.
-/


lemma initialSegment_ssubset {d k : ℕ} (hk : k < d) :
    initialSegment d k ⊂ initialSegment d (k + 1) := by
  simp +decide [ initialSegment, Finset.ssubset_def ];
  simp +decide [ Finset.subset_iff, le_iff_lt_or_eq ];
  exact ⟨ fun x hx => Or.inl hx, ⟨ ⟨ k, hk ⟩, Or.inr rfl, Or.inr rfl ⟩ ⟩

/-
Along the canonical chain, a weak embedding has strictly increasing ranks.
-/
lemma embedded_chain_rank_strict {α : Type*} [DecidableEq α] {d : ℕ}
    (f : Finset (Fin d) → Finset α)
    (hf : ∀ ⦃A B⦄, A ⊂ B → f A ⊂ f B)
    {i j : ℕ} (hij : i < j) (hj : j ≤ d) :
    (f (initialSegment d i)).card < (f (initialSegment d j)).card := by
  induction' hij with k hk;
  · exact Finset.card_lt_card ( hf ( initialSegment_ssubset ( Nat.lt_of_succ_le hj ) ) );
  · exact lt_trans ( by solve_by_elim [ Nat.le_of_succ_le ] ) ( Finset.card_lt_card ( hf ( initialSegment_ssubset ( by linarith ) ) ) )

/-
**Arbitrary-rank obstruction.** If a family occupies at most `d` cardinality
ranks (not necessarily consecutive), then it has no weak `B_d`.
-/

/-
In particular, any family occupying any three ranks is weakly `B₃`-free.
-/

/-
The same arbitrary-three-rank obstruction excludes strong copies.
-/

/-
A weak copy needs all `2^d` of its elements, so cardinality alone can rule it out.
-/


/-
The four-rank chain really meets each of the four ranks.
-/

/-
**Disproof:** occupying `d+1` ranks does not force `B_d`; already for `d=3`,
the four-rank maximal chain is weakly `B₃`-free.
-/


/-
**Explicit strong-copy construction.** Distinct generators outside the base
produce a strong copy of `B_d`; inclusion is both preserved and reflected.
-/

/-
Consequently, the full power set on `Fin d` contains a strong `B_d`.
-/


open B3FreeContrarian in
theorem solution{α : Type*} [DecidableEq α]
    {d : ℕ} (F : Finset (Finset α)) (R : Finset ℕ)
    (hR : R.card ≤ d) (hsupport : ∀ A ∈ F, A.card ∈ R) :
    WeakCubeFree d F := by
  intro h
  obtain ⟨f, hf_inj, hf_F, hf_strict⟩ := h
  have h_card : ∀ i : Fin (d + 1), (f (initialSegment d i)).card ∈ R := by
    exact fun i => hsupport _ ( hf_F _ );
  have h_distinct : ∀ i j : Fin (d + 1), i ≠ j → (f (initialSegment d i)).card ≠ (f (initialSegment d j)).card := by
    intro i j hij h_eq
    have h_lt : i.val < j.val ∨ j.val < i.val := by
      exact lt_or_gt_of_ne ( by simpa [ Fin.ext_iff ] using hij )
    cases' h_lt with h_lt h_lt
    generalize_proofs at *;
    · have := @embedded_chain_rank_strict α _ d f hf_strict i.val j.val h_lt ( by linarith [ Fin.is_lt j ] ) ; aesop;
    · have := @embedded_chain_rank_strict α _ d f hf_strict j i h_lt ( by linarith [ Fin.is_lt i, Fin.is_lt j ] ) ; aesop;
  exact absurd ( Finset.card_le_card ( show Finset.image ( fun i : Fin ( d + 1 ) => # ( f ( initialSegment d i ) ) ) Finset.univ ⊆ R from Finset.image_subset_iff.mpr fun i _ => h_card i ) ) ( by rw [ Finset.card_image_of_injective _ fun i j hij => not_imp_not.mp ( h_distinct i j ) hij ] ; simp +decide ; linarith )
