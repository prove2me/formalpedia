-- Prove2me | solution 1 for ShadowProfile.setShadowCard_uniformSlice_logConcave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:24:42.745164+00:00
-- url     : https://prove2.me/submissions/0d67df65-2176-4869-ac0b-86d7a3a3136a

import Mathlib
import Definitions.Def_Bridges_PosetTheory_ShadowLogConcavity

open Finset BigOperators ShadowProfile in
theorem solution (n r : ℕ) (hr : r ≤ n) :
    IsLogConcaveSeq (setShadowCard (uniformSlice n r) r) r := by
  -- the `k`-th shadow of the full `r`-slice is the full `(r - k)`-slice
  have hcard : ∀ k, k ≤ r → setShadowCard (uniformSlice n r) r k = n.choose (r - k) := by
    intro k hk
    have hset : setShadow (uniformSlice n r) r k = Finset.powersetCard (r - k) Finset.univ := by
      ext t
      simp only [setShadow, uniformSlice, Finset.mem_filter, Finset.mem_biUnion,
        Finset.mem_powerset, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · rintro ⟨-, htc⟩
        exact htc
      · intro ht
        obtain ⟨u, htu, -, hu⟩ := Finset.exists_subsuperset_card_eq (n := r) (Finset.subset_univ t)
          (by rw [ht]; omega) (by rw [Finset.card_univ, Fintype.card_fin]; exact hr)
        exact ⟨⟨u, hu, htu, ht⟩, ht⟩
    rw [setShadowCard, hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  intro k hk1 hk2
  show setShadowCard (uniformSlice n r) r k ^ 2
    ≥ setShadowCard (uniformSlice n r) r (k - 1) * setShadowCard (uniformSlice n r) r (k + 1)
  rw [hcard k (by omega), hcard (k - 1) (by omega), hcard (k + 1) hk2]
  obtain ⟨m, hm⟩ : ∃ m, r - (k + 1) = m := ⟨_, rfl⟩
  have e1 : r - k = m + 1 := by omega
  have e2 : r - (k - 1) = m + 2 := by omega
  rw [e1, e2, hm]
  -- binomial log-concavity `C(n,m) C(n,m+2) ≤ C(n,m+1)²`
  have h1 : n.choose (m + 1) * (m + 1) = n.choose m * (n - m) := Nat.choose_succ_right_eq n m
  have h2 : n.choose (m + 2) * (m + 2) = n.choose (m + 1) * (n - (m + 1)) :=
    Nat.choose_succ_right_eq n (m + 1)
  rcases Nat.lt_or_ge m n with hmn | hmn
  · have hpos : 0 < (m + 2) * (n - m) := Nat.mul_pos (by omega) (by omega)
    have h3 : (n - (m + 1)) * (m + 1) ≤ (m + 2) * (n - m) := by
      calc (n - (m + 1)) * (m + 1) ≤ (n - m) * (m + 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = (m + 2) * (n - m) := mul_comm _ _
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc n.choose (m + 2) * n.choose m * ((m + 2) * (n - m))
        = (n.choose (m + 2) * (m + 2)) * (n.choose m * (n - m)) := by ring
      _ = (n.choose (m + 1) * (n - (m + 1))) * (n.choose (m + 1) * (m + 1)) := by rw [h2, ← h1]
      _ = n.choose (m + 1) ^ 2 * ((n - (m + 1)) * (m + 1)) := by ring
      _ ≤ n.choose (m + 1) ^ 2 * ((m + 2) * (n - m)) := Nat.mul_le_mul_left _ h3
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < m + 2)]
    simp
