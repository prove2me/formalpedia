-- Prove2me | Theorems.Thm_CutIndexedSingleton_cutEntropy_le_card_mul_log
-- name    : CutIndexedSingleton.cutEntropy_le_card_mul_log
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:24:21.010188+00:00
-- url     : https://prove2.me/theorems/a8daf61f-9a5f-4e52-a54d-8416561a75dc
-- title:
--   CutEntropy le card mul log
-- statement:
--   Formal statement of `CutIndexedSingleton.cutEntropy_le_card_mul_log` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CutIndexedSingleton.cutEntropy_le_card_mul_log{C : Finset (Word n q)} (hC : C.Nonempty)
--       (S : Finset (Fin n)) : cutEntropy C S ≤ S.card * Real.log q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CutIndexedEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CutIndexedEntropy.lean#L137

-- Thm stub generated from Novelty/CutIndexedEntropy.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkEntropy

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

theorem CutIndexedSingleton.cutEntropy_le_card_mul_log{C : Finset (Word n q)} (hC : C.Nonempty)
    (S : Finset (Fin n)) : cutEntropy C S ≤ S.card * Real.log q := by sorry
