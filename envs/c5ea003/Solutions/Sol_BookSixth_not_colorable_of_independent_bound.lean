-- Prove2me | solution 1 for BookSixth.not_colorable_of_independent_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T17:57:51.414883+00:00
-- url     : https://prove2.me/submissions/517ca8c0-d252-4efb-9184-a140da2a8e52

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open Finset BookSixth

theorem solution {N k a : ℕ} (G : SimpleGraph (Fin N))
    (hind : ∀ S : Finset (Fin N),
      (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) → S.card ≤ a)
    (hsize : k * a < N) : ¬ HasColoring G k := by
  classical
  rintro ⟨c, hc⟩
  have hfiber (i : Fin k) : (univ.filter (fun v => c v = i)).card ≤ a := by
    apply hind
    intro u hu v hv huv
    exact hc u v huv ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
  have hcount : N = ∑ i : Fin k, (univ.filter (fun v => c v = i)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (univ : Finset (Fin N))) (t := (univ : Finset (Fin k)))
      (f := c) (fun _ _ => mem_univ _))
  have hle : N ≤ k * a := by
    calc
      N = ∑ i : Fin k, (univ.filter (fun v => c v = i)).card := hcount
      _ ≤ ∑ _i : Fin k, a := sum_le_sum (fun i _ => hfiber i)
      _ = k * a := by simp
  omega
