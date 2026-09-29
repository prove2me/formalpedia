-- Prove2me | solution 1 for SymplecticMatrix.standardFamily_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T17:02:28.822436+00:00
-- url     : https://prove2.me/submissions/3dad513d-5e28-4a89-9d59-779218334740

import Definitions.Def_symplectic_block_generators

open Matrix SymplecticMatrix

variable {l : ℕ} {R : Type*} [CommRing R]

abbrev SIdx (l : ℕ) := (Fin l × Fin l) ⊕ {p : Fin l × Fin l // p.1 ≤ p.2} ⊕
  {p : Fin l × Fin l // p.1 ≤ p.2}

noncomputable def sfam (l : ℕ) (R : Type*) [CommRing R] :
    SIdx l → Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R :=
  Sum.elim (fun p => elemX p.1 p.2)
    (Sum.elim (fun p => elemT p.1.1 p.1.2) (fun p => elemS p.1.1 p.1.2))

private lemma symmMatrix_apply (i j x y : Fin l) :
    (symmMatrix i j : Matrix (Fin l) (Fin l) R) x y
      = (if i = x ∧ j = y then 1 else 0) + (if i ≠ j ∧ j = x ∧ i = y then 1 else 0) := by
  by_cases h : i = j
  · subst h; simp [symmMatrix, Matrix.single]
  · simp [symmMatrix, h, Matrix.single]

private lemma symm_entry (p q : {p : Fin l × Fin l // p.1 ≤ p.2}) :
    (symmMatrix q.1.1 q.1.2 : Matrix (Fin l) (Fin l) R) p.1.1 p.1.2
      = if q = p then 1 else 0 := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  obtain ⟨⟨k, m⟩, hkm⟩ := q
  rw [symmMatrix_apply]
  have h2 : ¬(k ≠ m ∧ m = i ∧ k = j) := by
    rintro ⟨hne, rfl, rfl⟩
    exact hne (le_antisymm hkm hij)
  rw [if_neg h2, add_zero]
  by_cases h : k = i ∧ m = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by simpa [Subtype.ext_iff, Prod.ext_iff] using hc)


private lemma entryX (i j : Fin l) (x : SIdx l) :
    sfam l R x (Sum.inl i) (Sum.inl j) = if x = Sum.inl (i, j) then 1 else 0 := by
  rcases x with p | (q | q)
  · simp only [sfam, Sum.elim_inl, elemX, Matrix.fromBlocks_apply₁₁, Matrix.single,
      Matrix.of_apply, Sum.inl.injEq]
    by_cases h : p = (i, j)
    · subst h; simp
    · rw [if_neg (fun hc => h (Prod.ext hc.1 hc.2)), if_neg h]
  · simp [sfam, elemT]
  · simp [sfam, elemS]

private lemma entryT (q : {p : Fin l × Fin l // p.1 ≤ p.2}) (x : SIdx l) :
    sfam l R x (Sum.inl q.1.1) (Sum.inr q.1.2) = if x = Sum.inr (Sum.inl q) then 1 else 0 := by
  rcases x with p | (r | r)
  · simp [sfam, elemX]
  · simp only [sfam, Sum.elim_inr, Sum.elim_inl, elemT, Matrix.fromBlocks_apply₁₂,
      symm_entry q r, Sum.inr.injEq, Sum.inl.injEq]
  · simp [sfam, elemS]

private lemma entryS (q : {p : Fin l × Fin l // p.1 ≤ p.2}) (x : SIdx l) :
    sfam l R x (Sum.inr q.1.1) (Sum.inl q.1.2) = if x = Sum.inr (Sum.inr q) then 1 else 0 := by
  rcases x with p | (r | r)
  · simp [sfam, elemX]
  · simp [sfam, elemT]
  · simp only [sfam, Sum.elim_inr, elemS, Matrix.fromBlocks_apply₂₁,
      symm_entry q r, Sum.inr.injEq]

theorem solution (l : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R
      (Sum.elim (fun p : Fin l × Fin l =>
          (elemX p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R))
        (Sum.elim (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemT p.1.1 p.1.2)
          (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemS p.1.1 p.1.2))) := by
  classical
  show LinearIndependent R (sfam l R)
  rw [linearIndependent_iff']
  intro s g hg x hx
  have hentry : ∀ r c : Fin l ⊕ Fin l, ∑ y ∈ s, g y * sfam l R y r c = 0 := by
    intro r c
    have h := congrFun (congrFun hg r) c
    simpa [Matrix.sum_apply] using h
  have extract : ∀ (t : SIdx l) (r c : Fin l ⊕ Fin l),
      (∀ y : SIdx l, sfam l R y r c = if y = t then 1 else 0) → t ∈ s → g t = 0 := by
    intro t r c hval ht
    have h := hentry r c
    simp only [hval, mul_ite, mul_one, mul_zero] at h
    rwa [Finset.sum_ite_eq' s t g, if_pos ht] at h
  rcases x with p | (q | q)
  · exact extract _ (Sum.inl p.1) (Sum.inl p.2) (fun y => by simpa using entryX p.1 p.2 y) hx
  · exact extract _ (Sum.inl q.1.1) (Sum.inr q.1.2) (fun y => entryT q y) hx
  · exact extract _ (Sum.inr q.1.1) (Sum.inl q.1.2) (fun y => entryS q y) hx
