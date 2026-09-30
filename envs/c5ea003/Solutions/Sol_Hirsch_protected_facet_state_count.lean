-- Prove2me | solution 1 for Hirsch.protected_facet_state_count
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-16T23:47:35.557261+00:00
-- url     : https://prove2.me/submissions/e7971398-7465-4b52-b8bc-8bd07fd31f4a

import Mathlib

open scoped BigOperators

namespace Hirsch.ProtectedFacetCount

/-- Protected labels that have occurred by time i, including the current state. -/
def Seen {n : ℕ} (P : Fin n → Finset ℕ) (B : Finset ℕ) (i : Fin n) : Finset ℕ :=
  (Finset.univ.filter (fun j : Fin n => j ≤ i)).biUnion (fun j => P j \ B)

lemma mem_seen {n : ℕ} {P : Fin n → Finset ℕ} {B : Finset ℕ}
    {i : Fin n} {a : ℕ} :
    a ∈ Seen P B i ↔ ∃ j : Fin n, j ≤ i ∧ a ∈ P j ∧ a ∉ B := by
  simp [Seen, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_sdiff, and_assoc]

lemma current_subset_seen {n : ℕ} (P : Fin n → Finset ℕ)
    (B : Finset ℕ) (i : Fin n) : P i \ B ⊆ Seen P B i := by
  intro a ha
  obtain ⟨hp, hb⟩ := Finset.mem_sdiff.mp ha
  exact mem_seen.mpr ⟨i, le_rfl, hp, hb⟩

lemma seen_mono {n : ℕ} (P : Fin n → Finset ℕ) (B : Finset ℕ)
    {i j : Fin n} (hij : i ≤ j) : Seen P B i ⊆ Seen P B j := by
  intro a ha
  obtain ⟨k, hki, hk, hb⟩ := mem_seen.mp ha
  exact mem_seen.mpr ⟨k, hki.trans hij, hk, hb⟩

lemma seen_subset {n : ℕ} (V B : Finset ℕ) (P : Fin n → Finset ℕ)
    (hV : ∀ i, P i ⊆ V) (i : Fin n) : Seen P B i ⊆ V \ B := by
  intro a ha
  obtain ⟨k, _hki, hk, hb⟩ := mem_seen.mp ha
  exact Finset.mem_sdiff.mpr ⟨hV k hk, hb⟩

/-- The count of previously seen protected labels not active in the current state. -/
def Retired {n : ℕ} (P : Fin n → Finset ℕ) (B : Finset ℕ) (i : Fin n) : ℕ :=
  (Seen P B i \ (P i \ B)).card

lemma retired_add_current {n : ℕ} (P : Fin n → Finset ℕ)
    (B : Finset ℕ) (i : Fin n) :
    Retired P B i + (P i \ B).card = (Seen P B i).card := by
  exact Finset.card_sdiff_add_card_eq_card (current_subset_seen P B i)

lemma protected_card {n d : ℕ} (P : Fin n → Finset ℕ)
    (B : Finset ℕ) (hcard : ∀ i, (P i).card = d) (i : Fin n) :
    (P i \ B).card = d - (P i ∩ B).card := by
  have h := Finset.card_sdiff_add_card_inter (P i) B
  rw [hcard i] at h
  omega

lemma retired_le_excess {n d : ℕ} (V B : Finset ℕ)
    (P : Fin n → Finset ℕ) (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d) (i : Fin n) :
    Retired P B i ≤ V.card - d := by
  have hsub : Seen P B i \ (P i \ B) ⊆ V \ P i := by
    intro a ha
    obtain ⟨hs, hnot⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨k, _hki, hk, hb⟩ := mem_seen.mp hs
    refine Finset.mem_sdiff.mpr ⟨hV k hk, ?_⟩
    intro hp
    exact hnot (Finset.mem_sdiff.mpr ⟨hp, hb⟩)
  have h := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (hV i), hcard i] at h
  exact h

lemma retired_le_signature_capacity {n d : ℕ} (V B : Finset ℕ)
    (P : Fin n → Finset ℕ) (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d) (i : Fin n) :
    Retired P B i ≤ (V \ B).card - (d - (P i ∩ B).card) := by
  have hs : (Seen P B i).card ≤ (V \ B).card :=
    Finset.card_le_card (seen_subset V B P hV i)
  have hc := retired_add_current P B i
  rw [protected_card P B hcard i] at hc
  omega

/-- With interval membership for protected labels, equal seen sets and equal
exceptional signatures force equal current states. -/
lemma state_eq_of_seen_eq {n d : ℕ} (P : Fin n → Finset ℕ) (B : Finset ℕ)
    (hcard : ∀ i, (P i).card = d)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j)
    {i j : Fin n} (hij : i ≤ j) (hseen : Seen P B i = Seen P B j)
    (hsig : P i ∩ B = P j ∩ B) : P i = P j := by
  have hsub : P j ⊆ P i := by
    intro a ha
    by_cases hb : a ∈ B
    · have hm : a ∈ P j ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
      rw [← hsig] at hm
      exact (Finset.mem_inter.mp hm).1
    · have hm : a ∈ Seen P B j :=
        current_subset_seen P B j (Finset.mem_sdiff.mpr ⟨ha, hb⟩)
      rw [← hseen] at hm
      obtain ⟨k, hki, hk, _hkb⟩ := mem_seen.mp hm
      exact hinterval a hb k i j hki hij hk ha
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard i, hcard j])).symm

/-- A state is encoded by its active exceptional subset and its retired count.
No per-signature visitation bound is assumed. -/
theorem signature_retired_injective {n d : ℕ} (P : Fin n → Finset ℕ)
    (B : Finset ℕ) (hcard : ∀ i, (P i).card = d)
    (hinj : Function.Injective P)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j) :
    Function.Injective (fun i => (P i ∩ B, Retired P B i)) := by
  have ordered_case : ∀ i j : Fin n, i ≤ j →
      P i ∩ B = P j ∩ B → Retired P B i = Retired P B j → i = j := by
    intro i j hij hsig hret
    have hi := retired_add_current P B i
    have hj := retired_add_current P B j
    have hc : (P i \ B).card = (P j \ B).card := by
      rw [protected_card P B hcard i, protected_card P B hcard j, hsig]
    have hseen_card : (Seen P B i).card = (Seen P B j).card := by omega
    have hseen : Seen P B i = Seen P B j :=
      Finset.eq_of_subset_of_card_le (seen_mono P B hij) hseen_card.ge
    exact hinj (state_eq_of_seen_eq P B hcard hinterval hij hseen hsig)
  intro i j h
  have hsig : P i ∩ B = P j ∩ B := congrArg Prod.fst h
  have hret : Retired P B i = Retired P B j := congrArg Prod.snd h
  rcases le_total i j with hij | hji
  · exact ordered_case i j hij hsig hret
  · exact (ordered_case j i hji hsig.symm hret.symm).symm

/-- Any finite family of allowed exceptional signatures gives a weighted bound.
Impossible signatures can be excluded without classifying all polytope vertices. -/
theorem allowed_signature_bound {n d : ℕ} (V B : Finset ℕ)
    (P : Fin n → Finset ℕ) (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d) (hinj : Function.Injective P)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j)
    (C : Finset (Finset ℕ)) (hC : ∀ i, P i ∩ B ∈ C) :
    n ≤ ∑ S ∈ C, ((V \ B).card - (d - S.card) + 1) := by
  classical
  let cap : Finset ℕ → ℕ := fun S => (V \ B).card - (d - S.card) + 1
  let T : Finset (Σ _ : Finset ℕ, ℕ) := C.sigma (fun S => Finset.range (cap S))
  let f : Fin n → (Σ _ : Finset ℕ, ℕ) := fun i => ⟨P i ∩ B, Retired P B i⟩
  have hmap : Set.MapsTo f (Finset.univ : Finset (Fin n)) T := by
    intro i _hi
    apply Finset.mem_sigma.mpr
    refine ⟨hC i, Finset.mem_range.mpr ?_⟩
    have h := retired_le_signature_capacity V B P hV hcard i
    dsimp only [f, cap]
    omega
  have hf : Set.InjOn f (Finset.univ : Finset (Fin n)) := by
    intro i _hi j _hj h
    apply signature_retired_injective P B hcard hinj hinterval
    exact congrArg (fun p : (Σ _ : Finset ℕ, ℕ) => (p.1, p.2)) h
  have hle := Finset.card_le_card_of_injOn f hmap hf
  have hcount : T.card = ∑ S ∈ C, cap S := by
    calc
      T.card = ∑ _p ∈ T, (1 : ℕ) := by simp
      _ = ∑ S ∈ C, ∑ _j ∈ Finset.range (cap S), (1 : ℕ) :=
        Finset.sum_sigma C (fun S => Finset.range (cap S)) (fun _ => (1 : ℕ))
      _ = ∑ S ∈ C, cap S := by simp
  rw [hcount] at hle
  simpa only [Finset.card_univ, Fintype.card_fin, cap] using hle

/-- A certified registry of actual exceptional signatures suffices; it need
not enumerate the whole powerset or the polytope's entire vertex set. -/
theorem registry_bound {n d : ℕ} (V B : Finset ℕ)
    (P : Fin n → Finset ℕ) (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d) (hinj : Function.Injective P)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j)
    (C : Finset (Finset ℕ)) (hC : ∀ i, P i ∩ B ∈ C) :
    n ≤ (V.card - d + 1) * C.card := by
  classical
  let T : Finset (Finset ℕ × ℕ) :=
    C.product (Finset.range (V.card - d + 1))
  let f : Fin n → Finset ℕ × ℕ := fun i => (P i ∩ B, Retired P B i)
  have hmap : Set.MapsTo f (Finset.univ : Finset (Fin n)) T := by
    intro i _hi
    apply Finset.mem_product.mpr
    refine ⟨hC i, Finset.mem_range.mpr ?_⟩
    have h := retired_le_excess V B P hV hcard i
    dsimp only [f]
    omega
  have hf : Set.InjOn f (Finset.univ : Finset (Fin n)) := by
    intro i _hi j _hj h
    exact signature_retired_injective P B hcard hinj hinterval h
  have h := Finset.card_le_card_of_injOn f hmap hf
  simpa [T, Finset.card_product, Nat.mul_comm] using h

/-- The general count is linear in facet excess for a fixed exception set. -/
theorem power_bound {n d : ℕ} (V B : Finset ℕ)
    (P : Fin n → Finset ℕ) (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d) (hinj : Function.Injective P)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j) :
    n ≤ (V.card - d + 1) * 2 ^ B.card := by
  have hC : ∀ i, P i ∩ B ∈ B.powerset := by
    intro i
    exact Finset.mem_powerset.mpr Finset.inter_subset_right
  have h := registry_bound V B P hV hcard hinj hinterval B.powerset hC
  simpa only [Finset.card_powerset] using h

end Hirsch.ProtectedFacetCount

/-- Exact finite counting core for routes with a bounded exceptional facet set.
The geometric existence of such a route or a small exception set is not assumed
as a hidden conclusion: interval membership and distinct states are explicit. -/
theorem solution
    (n d : ℕ) (V B : Finset ℕ) (P : Fin n → Finset ℕ)
    (hV : ∀ i, P i ⊆ V)
    (hcard : ∀ i, (P i).card = d)
    (hinj : Function.Injective P)
    (hinterval : ∀ a, a ∉ B → ∀ i j k : Fin n, i ≤ j → j ≤ k →
      a ∈ P i → a ∈ P k → a ∈ P j) :
    n ≤ (V.card - d + 1) * 2 ^ B.card ∧
      ∀ C : Finset (Finset ℕ), (∀ i, P i ∩ B ∈ C) →
        n ≤ (V.card - d + 1) * C.card ∧
          n ≤ ∑ S ∈ C, ((V \ B).card - (d - S.card) + 1) := by
  refine ⟨Hirsch.ProtectedFacetCount.power_bound V B P hV hcard hinj hinterval, ?_⟩
  intro C hC
  exact ⟨Hirsch.ProtectedFacetCount.registry_bound V B P hV hcard hinj hinterval C hC,
    Hirsch.ProtectedFacetCount.allowed_signature_bound V B P hV hcard hinj hinterval C hC⟩

#print axioms Hirsch.ProtectedFacetCount.signature_retired_injective
#print axioms Hirsch.ProtectedFacetCount.allowed_signature_bound
#print axioms Hirsch.ProtectedFacetCount.registry_bound
#print axioms Hirsch.ProtectedFacetCount.power_bound
#print axioms solution
