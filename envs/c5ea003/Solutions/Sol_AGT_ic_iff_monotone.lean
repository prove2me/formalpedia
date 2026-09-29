-- Prove2me | solution 1 for AGT.ic_iff_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T19:01:51.536552+00:00
-- url     : https://prove2.me/submissions/5bf10caa-a593-4a50-9b1f-0f46ffd89c01

import Definitions.Def_agt_social

open AGT

/-- **Proposition 9.6 of *Algorithmic Game Theory***: a social choice
function is incentive compatible if and only if it is monotone. -/
theorem solution {A ι : Type*} [DecidableEq ι]
    (f : (ι → A → A → Prop) → A) :
    IncentiveCompatible f ↔ SCFMonotone f := by
  constructor
  · intro hic P hP i r' hr' hne
    haveI := hP i
    haveI := hr'
    have h1 : ¬ P i (f (Function.update P i r')) (f P) := hic P hP i r' hr'
    have hQP : IsPrefProfile (Function.update P i r') := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa [Function.update_self] using hr'
      · simpa [Function.update_of_ne hj] using hP j
    have hupd : Function.update (Function.update P i r') i (P i) = P := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    have h2 := hic (Function.update P i r') hQP i (P i) (hP i)
    rw [hupd] at h2
    rw [Function.update_self] at h2
    refine ⟨?_, ?_⟩
    · rcases trichotomous_of (P i) (f P) (f (Function.update P i r')) with h | h | h
      · exact h
      · exact absurd h hne
      · exact absurd h h1
    · rcases trichotomous_of r' (f (Function.update P i r')) (f P) with h | h | h
      · exact h
      · exact absurd h.symm hne
      · exact absurd h h2
  · intro hmono P hP i r' hr' hcon
    haveI := hP i
    have hne : f P ≠ f (Function.update P i r') := by
      intro h
      rw [← h] at hcon
      exact irrefl_of (P i) (f P) hcon
    have := (hmono P hP i r' hr' hne).1
    exact asymm_of (P i) this hcon
