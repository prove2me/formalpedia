-- Prove2me | Definitions.Def_Probability_BayesianWerewolf
-- name    : Probability_BayesianWerewolf
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:40.113761+00:00
-- url     : https://prove2.me/theorems/669bd2fc-d3d5-4533-98d0-28fadfc7db64
-- title:
--   Aether Catalog definitions — Probability_BayesianWerewolf
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.BayesianWerewolf`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/BayesianWerewolf.lean by skeleton subtraction
import Mathlib

/-!
# Bayesian one-step decisions in Werewolf

This file isolates the part of Bayesian Werewolf that is independent of a particular
behavioural and information model.  A player's unnormalised posterior score is the
product of their prior and the likelihood of the observed evidence.  The main result
proves that eliminating a player of maximal score is optimal for the one-step objective
of eliminating a werewolf.  A second result shows that randomisation cannot improve
this objective.

These are deliberately one-step theorems: maximizing the chance of today's correct
elimination need not maximize the probability of eventually winning a dynamic game
when actions also affect future information.
-/

namespace BayesianWerewolf

/-- The unnormalised Bayesian score of player `i`. -/
def score {ι : Type*} (prior likelihood : ι → ℝ) (i : ι) : ℝ :=
  prior i * likelihood i

/-- The posterior distribution obtained by normalising Bayesian scores on a finite type. -/
noncomputable def posterior {ι : Type*} [Fintype ι] (prior likelihood : ι → ℝ) (i : ι) : ℝ :=
  score prior likelihood i / ∑ j, score prior likelihood j








end BayesianWerewolf


