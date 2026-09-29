-- Prove2me | solution 1 for mme_recursive_region_computed_hash_selection
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:54:04.999278+00:00
-- url     : https://prove2.me/submissions/f7d7a17a-9f84-4f44-a453-0bad87df8cb6

import Definitions.Def_mme_recursive_region_hash_loads
import Theorems.Thm_mme_common_hash_scale_realization
import Theorems.Thm_mme_recursive_yz_simultaneous_usable_isolation

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem denominator_positive {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (j : LoadIndex half R ell parent n) : 0 < loadDen m j := by
  classical
  rcases j with u | ⟨i,a,f⟩
  · exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
  · dsimp [loadDen]
    letI : Nonempty {g : Position n → CompleteSplit.CompleteWord ell //
        ParentType (RecursiveXHash.block (yzMode i) a)
          (parentCounts (RecursiveXHash.block (yzMode i) a) f) g} :=
      ⟨⟨f, by intro r j w; rfl⟩⟩
    exact Nat.card_pos

theorem solution {half R ell N : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (d : ℕ)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (keep : Fin 2 → Address half R parent n → (Position n → CompleteSplit.CompleteWord ell) → Prop)
    (htype : ∀ i a, a ∈ RecursiveXHash.target m →
      8 * d * (typeHoles htotal (yzMode i) a (mu i) (keep i a)).card ≤
        (unbrokenWords htotal (yzMode i) a (mu i)).card) :
    let Q := commonScale half (loadNum htotal m d mu keep) (loadDen m)
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ half < p ∧ 2 * Q < p ∧ p ≤ 4 * Q ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧ ThreeAPFree (S : Set ℕ) ∧
      ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
        I ⊆ RecursiveXHash.target m ∧
        I ⊆ RecursiveXHash.bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
        I ⊆ RecursiveXHash.hashed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
        I ⊆ usable htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q d mu keep ∧
        (∀ a ∈ I, ∀ b ∈ RecursiveXHash.bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q,
          RecursiveXHash.block 0 a = RecursiveXHash.block 0 b → a = b) ∧
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ (I.card : ℝ) := by
  classical
  let Q := commonScale half (loadNum htotal m d mu keep) (loadDen m)
  obtain ⟨p,hprime,hodd,hgrade,hlow,hupp,hbudget,S,hSr,hSf,hSc,hlower⟩ :=
    mme_common_hash_scale_realization half (loadNum htotal m d mu keep) (loadDen m)
      (denominator_positive m)
  letI : Fact p.Prime := ⟨hprime⟩
  have hx : 8 * (RecursiveXHash.ambient (n := n) m).card ≤
      p * ((RecursiveXHash.ambient (n := n) m).image (RecursiveXHash.block 0)).card := by
    have hb := hbudget (.inl ())
    dsimp [loadNum, loadDen] at hb
    by_cases he : (RecursiveXHash.ambient (n := n) m).Nonempty
    · have hc : 1 ≤ ((RecursiveXHash.ambient (n := n) m).image (RecursiveXHash.block 0)).card :=
        Finset.card_pos.mpr (he.image _)
      simpa [max_eq_right hc] using hb
    · have hz : RecursiveXHash.ambient (n := n) m = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp [hz]
  have hyz : ∀ i a, a ∈ RecursiveXHash.target m →
      ∀ f ∈ unbrokenWords htotal (yzMode i) a (mu i), keep i a f →
        128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
          RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
            compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu i) ≤
          p * Nat.card {g : Position n → CompleteSplit.CompleteWord ell //
            ParentType (RecursiveXHash.block (yzMode i) a)
              (parentCounts (RecursiveXHash.block (yzMode i) a) f) g} := by
    intro i a ha f hf hk
    simpa [loadNum, loadDen, ha, hf, hk] using hbudget (.inr (i,a,f))
  obtain ⟨q,I,hIt,hIb,hIh,hIu,hIso,hIc⟩ :=
    mme_recursive_yz_simultaneous_usable_isolation parent n htotal m e S hSr hSf
      hodd hgrade d mu hmass keep htype hyz hx
  exact ⟨p,hprime,hodd,hgrade,hlow,hupp,S,hSr,hSf,q,I,hIt,hIb,hIh,hIu,hIso,
    hlower _ _ (Nat.cast_nonneg _) hIc⟩
