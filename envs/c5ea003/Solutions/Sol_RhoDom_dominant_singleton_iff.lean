-- Prove2me | solution 1 for RhoDom.dominant_singleton_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:21:53.23177+00:00
-- url     : https://prove2.me/submissions/b600e96e-272e-4f96-8747-3cd0a6c4d9a1

import Mathlib
import Definitions.Def_Novelty_RhoDominantCartan
open RhoDom Finset in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    IsRhoDominant G Finset.univ {v} ↔ 2 ≤ G.degree v := by
  -- `⟨β_V, α_iᵛ⟩ = 2 - deg i`
  have hbeta : ∀ i, betaPair G univ i = 2 - (G.degree i : ℤ) := by
    intro i
    unfold betaPair cartan
    have hsplit : ∀ j, (if i = j then (2 : ℤ) else if G.Adj i j then -1 else 0)
        = (if i = j then 2 else 0) + (if G.Adj i j then -1 else 0) := by
      intro j
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    rw [sum_congr rfl (fun j _ => hsplit j), sum_add_distrib, sum_ite_eq, if_pos (mem_univ _),
      ← sum_filter, sum_const, ← SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree]
    simp
    ring
  -- so the `i`-th coordinate of `λ_{{v},V}` is `deg i - A i v`
  have hpair : ∀ i, rhoDomPair G univ {v} i = G.degree i - cartan G i v := by
    intro i
    rw [rhoDomPair, hbeta, betaPair, sum_singleton]
    ring
  constructor
  · intro h
    have hv := h v
    rw [hpair] at hv
    simp only [cartan, if_true] at hv
    omega
  · intro h i
    rw [hpair]
    unfold cartan
    split_ifs with h1 h2
    · subst h1
      omega
    · omega
    · omega
