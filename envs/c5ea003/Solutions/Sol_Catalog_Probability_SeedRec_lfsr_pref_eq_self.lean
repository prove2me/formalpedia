-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_pref_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:54:55.872195+00:00
-- url     : https://prove2.me/submissions/bb3feaea-4afa-4d83-ae07-114e44954812

/-
# `Catalog.Probability.SeedRec.lfsr_pref_eq_self`
Target `d41c6fe8`. BINDERS from this target's OWN WA: [CommRing K] and NO [NeZero L],
even though the bundle declares `variable [NeZero L]` at line 52 ahead of the theorems.

DEFINITIONS: PRNG.stream g s t = g.out (g.step^[t] s); PRNG.pref g n s = fun i => g.stream s i;
lfsrStep shifts left (σ ⟨i+1⟩ while i+1 < L, feedback otherwise); lfsrOut reads cell 0.

MATHS. Iterating the shift t times and reading cell 0 returns σ t. The induction must be
GENERALISED over the register: `iterate_succ_apply` gives `step^[t+1] τ = step^[t] (step τ)`,
so the hypothesis is applied at `lfsrStep c τ`, not at `τ`.
-/
import Mathlib
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGLFSRDetection

set_option maxHeartbeats 400000

open Catalog.Probability.SeedRec Finset

open Catalog.Probability.SeedRec in
/-- **The target, verbatim.** -/
theorem solution {K : Type*} [CommRing K] {L : ℕ} (c σ : Fin L → K) :
    (lfsrPRNG c).pref L σ = σ := by
  have key : ∀ (t : ℕ) (τ : Fin L → K) (ht : t < L),
      lfsrOut ((lfsrStep c)^[t] τ) = τ ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero => intro τ ht; simp [lfsrOut, ht]
    | succ n ih =>
        intro τ ht
        rw [Function.iterate_succ_apply, ih (lfsrStep c τ) (by omega)]
        simp [lfsrStep, ht]
  funext i
  show lfsrOut ((lfsrStep c)^[(i : ℕ)] σ) = σ i
  rw [key (i : ℕ) σ i.isLt]
