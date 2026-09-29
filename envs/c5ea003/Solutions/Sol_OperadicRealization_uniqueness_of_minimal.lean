-- Prove2me | solution 1 for OperadicRealization.uniqueness_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:00:31.61598+00:00
-- url     : https://prove2.me/submissions/031bb757-080b-4126-b6cd-735347d9db08

import Mathlib
import Definitions.Def_Bridges_OperadicRealizationDuality

open OperadicRealization Function in
theorem solution {S : AlgSignature} {G Obs : Type} (A B : Architecture S G Obs)
    {sem : ObsSem S G Obs}
    (hA : Realizes A sem) (hB : Realizes B sem)
    (hsepA : ObsSeparated A) (hsepB : ObsSeparated B)
    (hreachA : Reachable A) (hreachB : Reachable B) :
    ∃ f : A.alg.carrier → B.alg.carrier,
      Bijective f ∧
      (∀ t : Term S G, f (A.state t) = B.state t) := by
  -- evaluating a context at a term's state is the state of the plugged term
  have hplug : ∀ (X : Architecture S G Obs) (c : Ctx S G) (t : Term S G),
      X.alg.evalCtx X.init c (X.state t) = X.state (c.plug t) := by
    intro X c t
    induction c with
    | hole => rfl
    | app op focus others sub ih =>
      simp only [SigAlgebra.evalCtx, Ctx.plug, Architecture.state, SigAlgebra.eval]
      congr 1
      funext j
      split_ifs
      · exact ih
      · rfl
  -- in a separated realization, equal states are exactly contextual equivalence
  have key : ∀ (X : Architecture S G Obs), Realizes X sem → ObsSeparated X →
      ∀ t u, X.state t = X.state u ↔ ctxEquiv sem t u := by
    intro X hX hsep t u
    have hX' : ∀ t, X.behavior t = sem t := hX
    constructor
    · intro h c
      rw [← hX', ← hX']
      simp only [Architecture.behavior]
      rw [← hplug X c t, ← hplug X c u, h]
    · intro h
      apply hsep
      intro c
      rw [hplug X c t, hplug X c u]
      have h2 := h c
      rw [← hX', ← hX'] at h2
      exact h2
  have hAB : ∀ t u, A.state t = A.state u ↔ B.state t = B.state u := fun t u =>
    (key A hA hsepA t u).trans (key B hB hsepB t u).symm
  have hsurjA : ∀ s, ∃ t, A.state t = s := hreachA
  have hsurjB : ∀ b, ∃ t, B.state t = b := hreachB
  choose pre hpre using hsurjA
  refine ⟨fun s => B.state (pre s), ⟨fun s1 s2 h => ?_, fun b => ?_⟩, fun t => ?_⟩
  · have h' : B.state (pre s1) = B.state (pre s2) := h
    have h3 := (hAB _ _).2 h'
    rwa [hpre, hpre] at h3
  · obtain ⟨t, rfl⟩ := hsurjB b
    exact ⟨A.state t, (hAB _ _).1 (hpre _)⟩
  · exact (hAB _ _).1 (hpre _)
