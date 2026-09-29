-- Prove2me | solution 1 for MarkovMixing.exists_unique_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:30:41.798948+00:00
-- url     : https://prove2.me/submissions/aee351d3-0b8f-4f86-bc96-1bc8e8d18cb4

import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_stationary_unique

open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) :
    ∃! π : V → ℝ, IsStationary P π := by
  obtain ⟨π, hstat, -, -⟩ := MarkovMixing.exists_stationary_pos P hP hirr
  refine ⟨π, hstat, ?_⟩
  intro π' hπ'
  exact MarkovMixing.stationary_unique P hP hirr π' π hπ' hstat
