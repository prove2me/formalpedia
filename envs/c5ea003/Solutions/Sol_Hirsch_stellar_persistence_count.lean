-- Prove2me | solution 1 for Hirsch.stellar_persistence_count
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-16T21:54:55.527762+00:00
-- url     : https://prove2.me/submissions/2807f578-7ed5-4be8-aa4a-4bc036ac3101

import Mathlib

namespace Hirsch.StellarPersistence

/-- Inclusion-minimal nonfaces, with all proper subsets required to be faces. -/
def MinimalNonface (K : Set (Finset ℕ)) (N : Finset ℕ) : Prop :=
  N ∉ K ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K

/-- The actual face-membership rule for stellar subdivision at E with fresh z. -/
def Stellar (K : Set (Finset ℕ)) (E : Finset ℕ) (z : ℕ) : Set (Finset ℕ) :=
  {T | if z ∈ T then
      (T.erase z ∪ E) ∈ K ∧ ¬ E ⊆ T.erase z
    else T ∈ K ∧ ¬ E ⊆ T}

/-- Canonical descendant of an old minimal nonface. -/
def Descendant (E : Finset ℕ) (z : ℕ) (N : Finset ℕ) : Finset ℕ :=
  if E ⊆ N then insert z (N \ E) else N

lemma mem_stellar_old {K : Set (Finset ℕ)} {E T : Finset ℕ} {z : ℕ}
    (hz : z ∉ T) :
    T ∈ Stellar K E z ↔ T ∈ K ∧ ¬ E ⊆ T := by
  simp [Stellar, hz]

lemma mem_stellar_new {K : Set (Finset ℕ)} {E T : Finset ℕ} {z : ℕ}
    (hz : z ∈ T) :
    T ∈ Stellar K E z ↔ (T.erase z ∪ E) ∈ K ∧ ¬ E ⊆ T.erase z := by
  simp [Stellar, hz]

lemma erase_descendant {E N : Finset ℕ} {z : ℕ}
    (hEN : E ⊆ N) (hzN : z ∉ N) :
    (insert z (N \ E)).erase z ∪ E = N := by
  ext a
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · rintro (⟨hneq, ha⟩ | ha)
    · rcases ha with heq | ha
      · exact False.elim (hneq heq)
      · exact ha.1
    · exact hEN ha
  · intro ha
    by_cases haE : a ∈ E
    · exact Or.inr haE
    · refine Or.inl ⟨?_, Or.inr ⟨ha, haE⟩⟩
      intro heq
      subst a
      exact hzN ha

lemma decode_descendant {E N : Finset ℕ} {z : ℕ} (hzN : z ∉ N) :
    (if z ∈ Descendant E z N then
      (Descendant E z N).erase z ∪ E else Descendant E z N) = N := by
  by_cases hEN : E ⊆ N
  · have hzD : z ∈ insert z (N \ E) := Finset.mem_insert_self _ _
    simpa only [Descendant, if_pos hEN, if_pos hzD] using erase_descendant hEN hzN
  · simp [Descendant, hEN, hzN]

lemma descendant_injective {E N M : Finset ℕ} {z : ℕ}
    (hzN : z ∉ N) (hzM : z ∉ M)
    (heq : Descendant E z N = Descendant E z M) : N = M := by
  calc
    N = (if z ∈ Descendant E z N then
        (Descendant E z N).erase z ∪ E else Descendant E z N) :=
      (decode_descendant hzN).symm
    _ = (if z ∈ Descendant E z M then
        (Descendant E z M).erase z ∪ E else Descendant E z M) := by rw [heq]
    _ = M := decode_descendant hzM

lemma edge_not_subset_insert_diff {E N : Finset ℕ} {z : ℕ}
    (hne : E.Nonempty) (hzE : z ∉ E) : ¬ E ⊆ insert z (N \ E) := by
  obtain ⟨a, ha⟩ := hne
  intro h
  rcases Finset.mem_insert.mp (h ha) with heq | hd
  · subst a
    exact hzE ha
  · exact (Finset.mem_sdiff.mp hd).2 ha

/-- Every old minimal nonface has its stated minimal descendant. -/
theorem minimal_descendant {K : Set (Finset ℕ)} {E N : Finset ℕ} {z : ℕ}
    (hne : E.Nonempty) (hzE : z ∉ E) (hzN : z ∉ N)
    (hN : MinimalNonface K N) :
    MinimalNonface (Stellar K E z) (Descendant E z N) := by
  by_cases hEN : E ⊆ N
  · simp only [Descendant, if_pos hEN]
    have hzD : z ∈ insert z (N \ E) := Finset.mem_insert_self _ _
    have hED : ¬ E ⊆ insert z (N \ E) := edge_not_subset_insert_diff hne hzE
    refine ⟨?_, ?_⟩
    · intro h
      have hk := ((mem_stellar_new hzD).mp h).1
      rw [erase_descendant hEN hzN] at hk
      exact hN.1 hk
    · intro T hT
      obtain ⟨hTD, hTne⟩ := Finset.ssubset_iff_subset_ne.mp hT
      have hET : ¬ E ⊆ T := fun h => hED (h.trans hTD)
      by_cases hzT : z ∈ T
      · apply (mem_stellar_new hzT).mpr
        have hUN : T.erase z ∪ E ⊆ N := by
          intro a ha
          rcases Finset.mem_union.mp ha with ht | he
          · have ht' := Finset.mem_erase.mp ht
            rcases Finset.mem_insert.mp (hTD ht'.2) with heq | hd
            · exact False.elim (ht'.1 heq)
            · exact (Finset.mem_sdiff.mp hd).1
          · exact hEN he
        have hUne : T.erase z ∪ E ≠ N := by
          intro heq
          apply hTne
          apply Finset.Subset.antisymm hTD
          intro a ha
          rcases Finset.mem_insert.mp ha with heqz | hd
          · subst a
            exact hzT
          · have had := Finset.mem_sdiff.mp hd
            have hau : a ∈ T.erase z ∪ E := by rw [heq]; exact had.1
            rcases Finset.mem_union.mp hau with ht | he
            · exact (Finset.mem_erase.mp ht).2
            · exact False.elim (had.2 he)
        refine ⟨hN.2 _ (Finset.ssubset_iff_subset_ne.mpr ⟨hUN, hUne⟩), ?_⟩
        intro h
        apply hET
        intro a ha
        exact (Finset.mem_erase.mp (h ha)).2
      · apply (mem_stellar_old hzT).mpr
        have hTN : T ⊆ N := by
          intro a ha
          rcases Finset.mem_insert.mp (hTD ha) with heq | hd
          · subst a
            exact False.elim (hzT ha)
          · exact (Finset.mem_sdiff.mp hd).1
        have hTneN : T ≠ N := by
          intro heq
          apply hET
          simpa only [heq] using hEN
        exact ⟨hN.2 T (Finset.ssubset_iff_subset_ne.mpr ⟨hTN, hTneN⟩), hET⟩
  · simp only [Descendant, if_neg hEN]
    refine ⟨fun h => hN.1 ((mem_stellar_old hzN).mp h).1, ?_⟩
    intro T hT
    have hTN := (Finset.ssubset_iff_subset_ne.mp hT).1
    have hzT : z ∉ T := fun h => hzN (hTN h)
    exact (mem_stellar_old hzT).mpr
      ⟨hN.2 T hT, fun h => hEN (h.trans hTN)⟩

/-- The subdivided face itself is an additional new minimal nonface. -/
theorem born_minimal {K : Set (Finset ℕ)} {E : Finset ℕ} {z : ℕ}
    (hdown : ∀ F ∈ K, ∀ T : Finset ℕ, T ⊆ F → T ∈ K)
    (hE : E ∈ K) (hzE : z ∉ E) :
    MinimalNonface (Stellar K E z) E := by
  refine ⟨?_, ?_⟩
  · intro h
    exact ((mem_stellar_old hzE).mp h).2 (fun _ ha => ha)
  · intro T hT
    obtain ⟨hTE, hTne⟩ := Finset.ssubset_iff_subset_ne.mp hT
    have hzT : z ∉ T := fun h => hzE (hTE h)
    refine (mem_stellar_old hzT).mpr ⟨hdown E hE T hTE, ?_⟩
    intro hET
    exact hTne (Finset.Subset.antisymm hTE hET)

lemma born_not_descendant {K : Set (Finset ℕ)} {E N : Finset ℕ} {z : ℕ}
    (hE : E ∈ K) (hzE : z ∉ E) (hzN : z ∉ N)
    (hN : MinimalNonface K N) : Descendant E z N ≠ E := by
  intro heq
  have hd := decode_descendant (E := E) hzN
  rw [heq] at hd
  have hEq : E = N := by simpa only [if_neg hzE] using hd
  exact hN.1 (hEq ▸ hE)

/-- A finite certified subfamily gains one distinct minimal nonface per step.
Completeness of the supplied old subfamily is not assumed. -/
theorem step_growth
    (V : Finset ℕ) (K : Set (Finset ℕ)) (E : Finset ℕ) (z : ℕ)
    (A : Finset (Finset ℕ))
    (hdown : ∀ F ∈ K, ∀ T : Finset ℕ, T ⊆ F → T ∈ K)
    (hsupport : ∀ F ∈ K, F ⊆ V)
    (hE : E ∈ K) (hsize : 2 ≤ E.card) (hz : z ∉ V)
    (hA : ∀ N ∈ A, N ⊆ V ∧ MinimalNonface K N) :
    ∃ B : Finset (Finset ℕ), B.card = A.card + 1 ∧
      ∀ N ∈ B, N ⊆ insert z V ∧ MinimalNonface (Stellar K E z) N := by
  classical
  have hEV : E ⊆ V := hsupport E hE
  have hzE : z ∉ E := fun h => hz (hEV h)
  have hne : E.Nonempty := Finset.card_pos.mp (by omega)
  have hf : Set.InjOn (Descendant E z) (A : Set (Finset ℕ)) := by
    intro N hN M hM heq
    exact descendant_injective
      (fun h => hz ((hA N hN).1 h))
      (fun h => hz ((hA M hM).1 h)) heq
  have hcard : (A.image (Descendant E z)).card = A.card :=
    Finset.card_image_iff.mpr hf
  have hnot : E ∉ A.image (Descendant E z) := by
    intro h
    obtain ⟨N, hN, heq⟩ := Finset.mem_image.mp h
    exact born_not_descendant hE hzE
      (fun h => hz ((hA N hN).1 h)) (hA N hN).2 heq
  refine ⟨insert E (A.image (Descendant E z)), ?_, ?_⟩
  · simp [hnot, hcard]
  · intro N hN
    rcases Finset.mem_insert.mp hN with heq | himg
    · subst N
      exact ⟨fun a ha => Finset.mem_insert_of_mem (hEV ha), born_minimal hdown hE hzE⟩
    · obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp himg
      have hMV := (hA M hM).1
      refine ⟨?_, minimal_descendant hne hzE (fun h => hz (hMV h)) (hA M hM).2⟩
      intro a ha
      by_cases hEM : E ⊆ M
      · simp only [Descendant, if_pos hEM] at ha
        rcases Finset.mem_insert.mp ha with heq | hd
        · subst a
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hMV (Finset.mem_sdiff.mp hd).1)
      · have haM : a ∈ M := by simpa only [Descendant, if_neg hEM] using ha
        exact Finset.mem_insert_of_mem (hMV haM)

/-- Actual finite stellar sequences preserve every certified root and add one
per subdivision. At flag completion the roots fit into the missing-pair slots. -/
theorem finite_sequence_bound
    (t : ℕ) (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ) (A : Finset (Finset ℕ))
    (hdown : ∀ i, i ≤ t → ∀ F ∈ K i, ∀ T : Finset ℕ, T ⊆ F → T ∈ K i)
    (hsupport : ∀ i, i ≤ t → ∀ F ∈ K i, F ⊆ V i)
    (hE : ∀ i, i < t → E i ∈ K i)
    (hsize : ∀ i, i < t → 2 ≤ (E i).card)
    (hz : ∀ i, i < t → z i ∉ V i)
    (hV : ∀ i, i < t → V (i+1) = insert (z i) (V i))
    (hstep : ∀ i, i < t → K (i+1) = Stellar (K i) (E i) (z i))
    (hA : ∀ N ∈ A, N ⊆ V 0 ∧ MinimalNonface (K 0) N)
    (hflag : ∀ N : Finset ℕ, N ⊆ V t → MinimalNonface (K t) N → N.card = 2) :
    A.card + t ≤ ((V 0).card + t).choose 2 := by
  classical
  have grow : ∀ i, i ≤ t → ∃ B : Finset (Finset ℕ),
      B.card = A.card + i ∧ ∀ N ∈ B, N ⊆ V i ∧ MinimalNonface (K i) N := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨A, by simp, hA⟩
    | succ i ih =>
      intro hi
      have hit : i < t := by omega
      have hile : i ≤ t := by omega
      obtain ⟨B, hBcard, hB⟩ := ih hile
      obtain ⟨C, hCcard, hC⟩ := step_growth (V i) (K i) (E i) (z i) B
        (hdown i hile) (hsupport i hile) (hE i hit) (hsize i hit) (hz i hit) hB
      refine ⟨C, by omega, ?_⟩
      intro N hN
      obtain ⟨hNV, hNK⟩ := hC N hN
      constructor
      · simpa only [Nat.succ_eq_add_one, hV i hit] using hNV
      · simpa only [Nat.succ_eq_add_one, hstep i hit] using hNK
  have vcard : ∀ i, i ≤ t → (V i).card = (V 0).card + i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hit : i < t := by omega
      have old := ih (by omega)
      rw [hV i hit]
      simpa [hz i hit, Nat.add_assoc] using congrArg (fun n : ℕ => n+1) old
  obtain ⟨B, hBcard, hB⟩ := grow t (Nat.le_refl t)
  have hsub : B ⊆ Finset.powersetCard 2 (V t) := by
    intro N hN
    exact Finset.mem_powersetCard.mpr ⟨(hB N hN).1, hflag N (hB N hN).1 (hB N hN).2⟩
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_powersetCard, hBcard, vcard t (Nat.le_refl t)] at hcount
  exact hcount

end Hirsch.StellarPersistence

/-- Formal count obstruction for any finite forward stellar flagification.
The stellar membership rule and minimality predicates are inlined so that the
platform target needs only an import, with no separately redeclared types. -/
theorem solution
    (t : ℕ) (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ) (A : Finset (Finset ℕ))
    (hdown : ∀ i, i ≤ t → ∀ F ∈ K i, ∀ T : Finset ℕ, T ⊆ F → T ∈ K i)
    (hsupport : ∀ i, i ≤ t → ∀ F ∈ K i, F ⊆ V i)
    (hE : ∀ i, i < t → E i ∈ K i)
    (hsize : ∀ i, i < t → 2 ≤ (E i).card)
    (hz : ∀ i, i < t → z i ∉ V i)
    (hV : ∀ i, i < t → V (i+1) = insert (z i) (V i))
    (hstep : ∀ i, i < t → K (i+1) =
      {T | if z i ∈ T then
        (T.erase (z i) ∪ E i) ∈ K i ∧ ¬ E i ⊆ T.erase (z i)
        else T ∈ K i ∧ ¬ E i ⊆ T})
    (hA : ∀ N ∈ A, N ⊆ V 0 ∧
      N ∉ K 0 ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K 0)
    (hflag : ∀ N : Finset ℕ, N ⊆ V t →
      (N ∉ K t ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K t) → N.card = 2) :
    A.card + t ≤ ((V 0).card + t).choose 2 := by
  exact Hirsch.StellarPersistence.finite_sequence_bound
    t V K E z A hdown hsupport hE hsize hz hV hstep hA hflag

#print axioms Hirsch.StellarPersistence.minimal_descendant
#print axioms Hirsch.StellarPersistence.born_minimal
#print axioms Hirsch.StellarPersistence.step_growth
#print axioms Hirsch.StellarPersistence.finite_sequence_bound
#print axioms solution
