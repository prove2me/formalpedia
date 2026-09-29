-- Prove2me | solution 2 for MarkovMixing.strong_stationary_bound
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:40:05.744067+00:00
-- url     : https://prove2.me/submissions/b9b53c5d-e313-495f-bffb-92731c28f1f8

import Theorems.Thm_MarkovMixing_tv_le_sep
import Theorems.Thm_MarkovMixing_sep_le_stopping_tail
import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_stationary_unique
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (hs : ∀ x : V, IsStrongStationaryTime P π x s) (t : ℕ) :
    distStationary P π t ≤ ⨆ x : V, stopTailProb P x s t := by
  classical
  -- the stationary distribution of an irreducible chain is positive
  obtain ⟨π', hst', hpos', -⟩ := MarkovMixing.exists_stationary_pos P hP hirr
  have hππ : π = π' := MarkovMixing.stationary_unique P hP hirr π π' hπ hst'
  have hpos : ∀ y : V, 0 < π y := by
    intro y; rw [hππ]; exact hpos' y
  have hbdd : BddAbove (Set.range fun x : V => stopTailProb P x s t) :=
    Set.Finite.bddAbove (Set.range fun x : V => stopTailProb P x s t).toFinite
  refine ciSup_le fun x => ?_
  calc tvDist (rowDist P t x) π ≤ sepDist P π x t :=
        MarkovMixing.tv_le_sep P hP π hπ hpos x t
    _ ≤ stopTailProb P x s t :=
        MarkovMixing.sep_le_stopping_tail P hP hirr π hπ s x (hs x) t
    _ ≤ ⨆ x : V, stopTailProb P x s t := le_ciSup hbdd x
