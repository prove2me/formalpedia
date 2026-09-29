-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.perfectlySimulates_of_bijection
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:40:33.910966+00:00
-- url     : https://prove2.me/submissions/085c7bb5-f6df-4a90-8722-48d7a7b12c4b

import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

open Finset MachineLearning.CommittedLocalOracleZK
set_option autoImplicit false

/- Attributed direct port: Paul Klemstine, Aether Catalog, commit 53c2925a02.
   Source: https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CommittedLocalOracleZK.lean#L191
   Proof body unchanged; exact binders follow saved server expected-telescope evidence. -/

theorem solution {I A C O Rc Rv P S : Type*}
    [DecidableEq I] [Fintype I] [Fintype P] [Fintype S] [DecidableEq A]
    {Pr : CommittedOracle I A C O Rc Rv P}
    {sim : Rv → S → I → A} (Φ : Rv → P → S) (hbij : ∀ r, Function.Bijective (Φ r))
    (hview : ∀ r p, restrictTo (Pr.Q r) (Pr.proof p) = restrictTo (Pr.Q r) (sim r (Φ r p))) :
    PerfectlySimulatesOpened Pr sim := by
  intro r t
  have hcards : Fintype.card P = Fintype.card S := Fintype.card_of_bijective (hbij r)
  have hfib : (univ.filter fun p : P => restrictTo (Pr.Q r) (Pr.proof p) = t).card
      = (univ.filter fun s : S => restrictTo (Pr.Q r) (sim r s) = t).card := by
    refine Finset.card_bij (fun p _ => Φ r p) ?_ ?_ ?_
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, by rw [← hview r p]; exact hp.2⟩
    · intro p _ q _ h
      exact (hbij r).1 h
    · intro s hs
      obtain ⟨p, hp⟩ := (hbij r).2 s
      refine ⟨p, ?_, hp⟩
      rw [mem_filter] at hs ⊢
      exact ⟨mem_univ _, by rw [hview r p, hp]; exact hs.2⟩
  rw [hfib, hcards]
