-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_pareto_monotone_neighbour_paths
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T18:49:34.053922+00:00
-- url     : https://prove2.me/submissions/09232188-8561-489a-889c-398cfecaa460

import Theorems.Thm_BanditAlgorithm_partial_monitoring_pareto_cover_ranked_descent

open scoped BigOperators

namespace BanditAlgorithm

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d) :
    ∃ S : Finset (Fin k),
      S.Nonempty ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
        ∃ root ∈ S, ∀ b ∈ S,
          ∃ m : ℕ, ∃ path : Fin (m + 1) → Fin k,
            m ≤ k ∧ path 0 = b ∧ path (Fin.last m) = root ∧
            (∀ t, path t ∈ S) ∧
            ∀ t : Fin m,
              NeighbouringActions G (path t.castSucc) (path t.succ) ∧
              ∑ i : Fin d, G.L (path t.succ) i * lam i ≤
                ∑ i : Fin d, G.L (path t.castSucc) i * lam i := by
  classical
  obtain ⟨S, hSne, hbest, hdesc⟩ :=
    partial_monitoring_pareto_cover_ranked_descent G hk hd
  refine ⟨S, hSne, hbest, ?_⟩
  intro lam hlam
  obtain ⟨root, hrootS, rank, hstep⟩ := hdesc lam hlam
  refine ⟨root, hrootS, ?_⟩
  let weight : Fin k → ℝ := fun a ↦ ∑ i : Fin d, G.L a i * lam i
  let parent : Fin k → Fin k := fun b ↦
    if hb : b ∈ S ∧ b ≠ root then Classical.choose (hstep b hb.1 hb.2) else b
  have parent_spec {b : Fin k} (hbS : b ∈ S) (hbr : b ≠ root) :
      parent b ∈ S ∧ NeighbouringActions G b (parent b) ∧
        weight (parent b) ≤ weight b ∧ rank (parent b) < rank b := by
    have hs := Classical.choose_spec (hstep b hbS hbr)
    simpa [parent, hbS, hbr, weight] using hs
  have parent_mem {b : Fin k} (hbS : b ∈ S) : parent b ∈ S := by
    by_cases hbr : b = root
    · subst b
      simpa [parent, hrootS]
    · exact (parent_spec hbS hbr).1
  have iterate_mem (b : Fin k) (hbS : b ∈ S) :
      ∀ n : ℕ, (parent^[n]) b ∈ S := by
    intro n
    induction n with
    | zero => simpa
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact parent_mem ih
  intro b hbS
  have hex : ∃ m : ℕ, m ≤ k ∧ (parent^[m]) b = root := by
    by_contra hnone
    push_neg at hnone
    let act : Fin (k + 1) → Fin k := fun t ↦ (parent^[t.val]) b
    let ranks : Fin (k + 1) → ℕ := fun t ↦ rank (act t)
    have hanti : StrictAnti ranks := by
      rw [Fin.strictAnti_iff_succ_lt]
      intro t
      have htroot : act t.castSucc ≠ root := by
        dsimp [act]
        exact hnone t.val (Nat.le_of_lt t.isLt)
      have htmem : act t.castSucc ∈ S := by
        dsimp [act]
        exact iterate_mem b hbS t.val
      have hs := (parent_spec htmem htroot).2.2.2
      have hactSucc : act t.succ = parent (act t.castSucc) := by
        dsimp [act]
        change (parent^[t.val]) (parent b) = parent ((parent^[t.val]) b)
        exact (Function.Commute.iterate_self parent t.val) b
      change rank (act t.succ) < rank (act t.castSucc)
      rw [hactSucc]
      exact hs
    have hactinj : Function.Injective act := by
      intro x y hxy
      apply hanti.injective
      exact congrArg rank hxy
    have hcard := Fintype.card_le_of_injective act hactinj
    simp only [Fintype.card_fin] at hcard
    omega
  let m := Nat.find hex
  have hm : m ≤ k ∧ (parent^[m]) b = root := Nat.find_spec hex
  have hbefore {t : ℕ} (ht : t < m) : (parent^[t]) b ≠ root := by
    intro heq
    exact (Nat.find_min hex ht) ⟨ht.le.trans hm.1, heq⟩
  let path : Fin (m + 1) → Fin k := fun t ↦ (parent^[t.val]) b
  refine ⟨m, path, hm.1, ?_, ?_, ?_, ?_⟩
  · simp [path]
  · simpa [path] using hm.2
  · intro t
    exact iterate_mem b hbS t.val
  · intro t
    have htmem : path t.castSucc ∈ S := iterate_mem b hbS t.val
    have htroot : path t.castSucc ≠ root := hbefore t.isLt
    have hs := parent_spec htmem htroot
    have hsucc : path t.succ = parent (path t.castSucc) := by
      simp only [path, Fin.val_succ, Fin.val_castSucc]
      rw [Function.iterate_succ_apply']
    rw [hsucc]
    exact ⟨hs.2.1, hs.2.2.1⟩
