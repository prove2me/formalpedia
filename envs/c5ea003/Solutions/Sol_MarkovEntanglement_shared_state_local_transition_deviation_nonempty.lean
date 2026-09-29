-- Prove2me | solution 1 for MarkovEntanglement.shared_state_local_transition_deviation_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T23:49:08.382606+00:00
-- url     : https://prove2.me/submissions/481f9708-786f-4ce2-9dd6-66c5e3ce5b8e

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (hP : IsTransitionMatrix P)
    (i : Fin N) (E : ℝ)
    (Pi Ptrue : Matrix (S i × Z) (S i × Z) ℝ) (hPi : IsTransitionMatrix Pi)
    (htrue : ∀ p t, marginalZ i P p t = Ptrue (p.1 i, p.2) t)
    (hE : ∀ p t, |marginalZ i P p t - Pi (p.1 i, p.2) t| ≤ E) :
    ∀ s t, |Ptrue s t - Pi s t| ≤ 2 * E := by
  classical
  intro s t
  obtain ⟨s1, z⟩ := s
  set f : Joint S := Function.update (fun j => Classical.arbitrary (S j)) i s1 with hf
  have hp1 : f i = s1 := by rw [hf]; exact Function.update_self i s1 _
  have h1 := htrue (f, z) t
  have h2 := hE (f, z) t
  dsimp only at h1 h2
  rw [hp1] at h1 h2
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) h2
  rw [← h1]
  linarith
