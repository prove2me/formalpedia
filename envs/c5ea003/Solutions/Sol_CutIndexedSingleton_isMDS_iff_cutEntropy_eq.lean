-- Prove2me | solution 1 for CutIndexedSingleton.isMDS_iff_cutEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:48:43.818587+00:00
-- url     : https://prove2.me/submissions/1241db3f-5caa-4e17-b779-14a00cba9e7f

-- Sol generated from Novelty/CutIndexedEntropy.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_CutIndexedSingleton_cutEntropy_le_log_cutRank
import Theorems.Thm_CutIndexedSingleton_cutEntropy_of_isMDS
import Theorems.Thm_CutIndexedSingleton_singleton_bound_of_minDist

/-!
# Cut-indexed defects II: the entropy profile of a cut

`CutIndexedSingleton.lean` proved the cut-wise Singleton inequality
`|C| ≤ q ^ (k - |S|) * cutRank C S` for the *counting* bond dimension of a code.
This file replaces counting by **Shannon entropy** and asks when the resulting
entropic inequality is an equality.

## The cut entropy

Put the uniform distribution on the codebook `C` and push it forward to the cut
`S`: the pattern `y : S → Fin q` receives probability
`cutProb C S y = |fibre over y| / |C|`.  Its Shannon entropy `cutEntropy C S` is
the entropy of the marginal seen by the sites in `S` — the classical shadow of
the entanglement entropy across the cut.

## Main results

* `sum_cutProb`, `support_cutProb` : `cutProb` is a probability vector whose
  support is exactly the set of realised patterns, of size `cutRank C S`;
* `cutEntropy_le_log_cutRank` : the entropy of a cut is at most the log of its
  bond dimension (reusing `IITTensorNetwork.sum_negMulLog_le_log_card_support`);
* `cutEntropy_le_min` : **entropic cut-wise Singleton.**  For a code of minimum
  distance `d`, `H(S) ≤ min (|S|, k) * log q` — the entropy profile is trapped
  under the "Ryu–Takayanagi"-shaped plateau curve;
* `entropyDefect_nonneg` : the *entropic cut defect* `|S| log q - H(S)` is
  nonnegative;
* `cutEntropy_of_isMDS` : **the plateau is attained.**  For an MDS code,
  `H(S) = min (|S|, k) * log q` at *every* cut: the profile rises with unit slope
  `log q` up to `|S| = k` and is exactly flat afterwards;
* `isMDS_iff_cutEntropy_eq` : **equality with entropy is equivalent to MDS.**
  Given minimum distance `d` and any single cut `S` of size `k`, the code is MDS
  if and only if the entropy of that one cut equals `k log q`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the combinatorial defect `q ^ (k-|S|) rank S - |C|`
should have an entropic avatar whose vanishing is *equivalent* to the MDS
property, and the entropy profile of an MDS code should be the piecewise-linear
`min(|S|, k) log q` — a discrete Ryu–Takayanagi curve with a sharp corner at the
Singleton dimension.

Experiment (Experimenter): both halves were proved.  The upward slope comes from
`fiber_card_of_isMDS` (balanced fibres force a *uniform* marginal on `q ^ |S|`
patterns); the plateau comes from `cutRank_eq_card_of_minDist` (above `k` the
projection is injective, so the marginal is uniform on all of `C`).  Both cases
are instances of one lemma, `cutEntropy_eq_log_of_uniform`.

Analysis (Analyst): the "needs a different definition" verdict of cycle 1 applies
to the converse direction: `H(S) = |S| log q` for a *single* cut of size `k` is
already enough for MDS, because Shannon entropy of the marginal never exceeds
`log |C|`.  So the whole Singleton defect is detectable at one cut — no averaging
over cuts is needed.  This is what makes `isMDS_iff_cutEntropy_eq` an `iff`.

Critique (Critic): the equivalence needs `2 ≤ q` (for `q = 1` all logs vanish and
the criterion is vacuous) and `C.Nonempty` (the empty code has no marginal); both
hypotheses are recorded explicitly and are necessary.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}













/-! ### Flat marginals -/





open CutIndexedSingleton in
theorem solution{C : Finset (Word n q)} {d : ℕ} (hC : C.Nonempty)
    (hd : MinDist C d) (hd1 : 1 ≤ d) (hdn : d ≤ n + 1) (hq : 2 ≤ q)
    {S : Finset (Fin n)} (hS : S.card = CutData.sdim n d) :
    IsMDS C d ↔ cutEntropy C S = (CutData.sdim n d : ℕ) * Real.log q := by
  classical
  set k := CutData.sdim n d with hk
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  constructor
  · intro hmds
    have := cutEntropy_of_isMDS hmds hd1 hdn hq0 S
    rwa [hS, Nat.min_self] at this
  · intro hent
    refine ⟨hd, ?_⟩
    have hle : C.card ≤ q ^ k := singleton_bound_of_minDist hd hd1
    have h1 : cutEntropy C S ≤ Real.log C.card := by
      have h2 := cutEntropy_le_log_cutRank hC S
      have h3 : (cutRank C S : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast Finset.card_image_le
      have hpos : (0 : ℝ) < cutRank C S := by
        have : 0 < cutRank C S := by
          rw [cutRank, Finset.card_pos]
          exact hC.image _
        exact_mod_cast this
      exact h2.trans (Real.log_le_log hpos h3)
    rw [hent] at h1
    have hCpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
    have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
    have hlog : Real.log ((q : ℝ) ^ k) ≤ Real.log C.card := by
      rw [Real.log_pow]
      exact_mod_cast h1
    have hge : ((q : ℝ)) ^ k ≤ (C.card : ℝ) := (Real.log_le_log_iff hqk hCpos).mp hlog
    have hge' : q ^ k ≤ C.card := by exact_mod_cast hge
    exact le_antisymm hle hge'
