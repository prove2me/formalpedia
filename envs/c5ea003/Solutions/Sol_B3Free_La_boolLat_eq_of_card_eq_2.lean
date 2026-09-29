-- Prove2me | solution 2 for B3Free.La_boolLat_eq_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:06:40.378304+00:00
-- url     : https://prove2.me/submissions/721beef5-92a3-4e68-8c85-5c0c40adcc13

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {d : ℕ} (hcard : Fintype.card α = d) :
    La α (BoolLat d) = 2 ^ d - 1 := by
  classical
  have hbig : ∀ {d : ℕ}, d ≤ Fintype.card α → ∃ ι : BoolLat d → Finset α, IsWeakCopy ι := by
    intro d hd
    obtain ⟨e⟩ : Nonempty (Fin d ↪ α) := Function.Embedding.nonempty_of_card_le (by simpa using hd)
    refine ⟨fun X => X.image e, Finset.image_injective e.injective, ?_⟩
    intro p q hpq
    have h1 : (p : Finset (Fin d)).image e ⊆ (q : Finset (Fin d)).image e :=
      Finset.image_subset_image (le_of_lt hpq)
    have h2 : (p : Finset (Fin d)).image e ≠ (q : Finset (Fin d)).image e := by
      intro hEq
      exact (ne_of_lt hpq) (Finset.image_injective e.injective hEq)
    exact Finset.ssubset_iff_subset_ne.mpr ⟨h1, h2⟩
  have hlt : ∀ {d : ℕ}, d ≤ Fintype.card α → La α (BoolLat d) < 2 ^ Fintype.card α := by
    intro d hd
    have hnotfree : ¬ WeakFree (Finset.univ : Finset (Finset α)) (BoolLat d) := by
      intro hfree
      obtain ⟨ι, hc⟩ := hbig hd
      exact hfree ⟨ι, hc, fun p => Finset.mem_univ _⟩
    have hcardf : Fintype.card (Finset α) = 2 ^ Fintype.card α := Fintype.card_finset
    unfold La
    rw [← hcardf]
    refine (Finset.sup_lt_iff (by rw [hcardf]; positivity)).mpr ?_
    intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    have hne : F ≠ Finset.univ := by
      intro hEq
      rw [hEq] at hF
      exact hnotfree hF
    have hle : F.card ≤ Fintype.card (Finset α) := by
      simpa using Finset.card_le_univ F
    have hneq : F.card ≠ Fintype.card (Finset α) := by
      intro hEq
      exact hne ((Finset.card_eq_iff_eq_univ F).mp hEq)
    omega
  have hupper : La α (BoolLat d) < 2 ^ d := by
    have := hlt (d := d) (by omega)
    rw [hcard] at this
    exact this
  have hcarddom : Fintype.card (BoolLat d) = 2 ^ d := by
    simp [BoolLat, Fintype.card_finset]
  have hfam : ((Finset.univ : Finset (Finset α)).erase ∅).card = 2 ^ d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset, hcard]
  have hF : WeakFree ((Finset.univ : Finset (Finset α)).erase ∅) (BoolLat d) := by
    rintro ⟨ι, hc, hmem⟩
    have h1 : (Finset.univ : Finset (BoolLat d)).card
        ≤ ((Finset.univ : Finset (Finset α)).erase ∅).card :=
      Finset.card_le_card_of_injOn ι (fun X _ => hmem X) (fun X _ Y _ hxy => hc.1 hxy)
    rw [Finset.card_univ, hcarddom, hfam] at h1
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega
  have hlower : 2 ^ d - 1 ≤ La α (BoolLat d) := by
    unfold La
    have hmemfilter : ((Finset.univ : Finset (Finset α)).erase ∅)
        ∈ (Finset.univ : Finset (Finset (Finset α))).filter (fun F => WeakFree F (BoolLat d)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩
    have := Finset.le_sup (f := Finset.card) hmemfilter
    rw [hfam] at this
    exact this
  omega
