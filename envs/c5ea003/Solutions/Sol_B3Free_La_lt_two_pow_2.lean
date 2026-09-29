-- Prove2me | solution 2 for B3Free.La_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:11:24.620216+00:00
-- url     : https://prove2.me/submissions/9803b4f4-5fcf-456a-b411-933b47cc2587

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {d : ℕ} (h : d ≤ Fintype.card α) :
    La α (BoolLat d) < 2 ^ Fintype.card α := by
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
  exact hlt h
