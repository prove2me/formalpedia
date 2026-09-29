-- Prove2me | Theorems.Thm_mme_global_CW_simultaneous_usable_incidence
-- name    : mme_global_CW_simultaneous_usable_incidence
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:56:12.547092+00:00
-- url     : https://prove2.me/theorems/94a8bd7d-e8b7-43c0-b381-20a741a485ad
-- title:
--   Simultaneous usable global hash incidences from multinomial loads
-- statement:
--   If each Y/Z target fiber times its exact compatibility count is at most the prime times its coarse-word count divided by 128 times the repair scale, then at least seven eighths of all retained target incidences simultaneously meet the required global hole fractions. No additional word-type concentration hypothesis is needed.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash MME.HashExtraction
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_simultaneous_usable_incidence {half R ell N p : ℕ} [Fact p.Prime]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (hpodd : Odd p) (hgrade : half < p) (d : ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2)
    (hbudget : ∀ i : Fin 2, ∀ a, a ∈ RecursiveXHash.target m →
      128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) ≤
          p * modeNumber (yzMode i) (mu (yzMode i))) :
    7 * (RecursiveXHash.target (n := n) m).card * S.card * p ^ (N+1) ≤
      8 * ∑ q : (Fin (N+2) → ZMod p) × ZMod p,
        (((RecursiveXHash.target m).filter (fun a ↦ a ∈ RecursiveXHash.hashed m e S q)) ∩
          hashUsable m e S q d mu).card := by
  sorry
