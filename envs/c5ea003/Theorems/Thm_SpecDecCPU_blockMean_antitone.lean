-- Prove2me | Theorems.Thm_SpecDecCPU_blockMean_antitone
-- name    : SpecDecCPU.blockMean_antitone
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:52:41.379339+00:00
-- url     : https://prove2.me/theorems/2ef3245c-9a15-4ba2-98d8-aabb885ccbca
-- title:
--   Falsifiable necessary condition.
-- statement:
--   **Falsifiable necessary condition.**  Monotone survival forces the mean acceptance of
--   the *positions between* two measured depths to be at most that of the earlier block.
--
--   ```lean
--   theorem SpecDecCPU.blockMean_antitone{S : ℕ → ℝ} (hS0 : S 0 = 1) (hS : ∀ k, S (k + 1) ≤ S k)
--       {d e : ℕ} (hde : d < e) :
--       (e - d : ℝ) * (posYield S d - 1) ≥ (d : ℝ) * (posYield S e - posYield S d) := by sorry
--   /-! ## The reconstructed NET-91 profiles -/
--
--
--
--
--
--
--
--
--
--
--
--
--
--   /-! ## The local stopping rule and the derived prescription -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SpeculativeDecodingAcceptanceProfiles.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SpeculativeDecodingAcceptanceProfiles.lean#L134

-- Thm stub generated from Shared/SpeculativeDecodingAcceptanceProfiles.lean
import Mathlib
import Definitions.Def_Shared_SpeculativeDecodingAcceptanceProfiles
import Definitions.Def_Shared_SpeculativeDecodingDepthUnimodality

/-!
# Per-position acceptance profiles: reconstructing the NET-91 acceptance maps

Cycle 3 of the NET-91 thread, attacking the experiment's first open question — *per-position
acceptance maps: why does prose collapse past `d = 4`?*

Cycle 1 proved that the reported acceptance percentages cannot be per-position independent
acceptance probabilities (`SpecDecCPU.iid_cannot_explain_code_depth8`).  The repair is to
model the **survival profile** directly: `S k` is the probability that the first `k`
drafted positions are all accepted, so `S 0 = 1`, `S` is nonincreasing, and the block yield
is `posYield S d = ∑_{k ≤ d} S k`.  The i.i.d. model is the special case `S k = a ^ k`.

## Results

* **Averaging law** (`meanAccept_antitone_succ`, `meanAccept_antitone`): for *any* fixed
  survival profile the reported overall acceptance — the mean `(posYield S d - 1)/d` — is
  automatically nonincreasing in depth.  So the measured decay of acceptance with depth
  (prose `63.9 → 47.7 → 30.9`, code `71.6 → 63.0 → 56.0`) is not evidence that the drafter
  degrades: it is forced by averaging a nonincreasing profile.
* **Falsifiable necessary condition** (`blockMean_antitone`, `meanAccept_antitone`):
  monotone survival forces the *block* means between successive measured depths to be
  nonincreasing as well.  The test has teeth — acceptance percentages rising with depth are
  unrealisable (`unrealisable_increasing_acceptance`) — and the NET-91 numbers pass it
  (`net91_acceptances_realisable`).
* **Exact reconstruction** (`code_profile_matches_measurements`,
  `prose_profile_matches_measurements`): explicit nonincreasing survival profiles that
  reproduce *all three* measured acceptance percentages of each domain exactly.  The
  reported numbers are therefore fully consistent with a single depth-independent
  per-position map, and the maps are exhibited.
* **Practical stopping rule** (`deepen_pays_iff_marginal_survival`): deepen the draft while
  the survival probability of the next position exceeds `c` times the current speedup.
  This is the exact optimality condition, and by cycle 2 it is safe to apply greedily.
* **The prescription, derived** (`prose_stops_at_four`, `code_pays_through_eight`): with
  the reconstructed profiles and a marginal per-position cost `k = 0.287` (the average
  marginal cost over depths 4 to 8 of the cost curve fitted in cycle 4), prose stops paying
  at depth 4 while code still gains from 4 to 8 — exactly the measured prescription
  "`d = 8` for code, `d = 4` for prose", now a theorem about the reconstructed profiles
  rather than a fitted observation.

-- !-- Lab Notes -- !--
Hypothesizer (cycle 3):
 (D1) [BOLD] The measured acceptance decay with depth carries *no* information about the
      drafter: any fixed profile produces a nonincreasing measured mean.
 (D2) [BOLD] The six measured acceptance numbers are exactly realisable by two monotone
      per-position maps; the "collapse" is a property of the tail of the prose map.
 (D3) Monotone survival is falsifiable from three depths per domain via block means.
 (D4) The optimal-depth rule is local: compare next-position survival with `c ·` current
      speedup.
 (D5) With the cycle-1 cost bracket, D2 + D4 reproduce the deployed prescription.

Experimenter: D1–D5 formalised below, zero sorries.  Reconstructed survival profiles
(probability that the first `k` drafted tokens are all accepted):

  k        :  0     1      2      3      4     5..8
  code     : 1.000 0.800  0.632  0.560  0.528  0.490
  prose    : 1.000 0.700  0.578  0.350  0.280  0.141

Block means (measured, cumulative differences): code 0.716, 0.544, 0.490; prose 0.639,
0.315, 0.141 — both nonincreasing, as monotone survival requires.

Analyst: the prose map falls off a cliff between positions 2 and 3 (0.578 → 0.350) whereas
the code map decays gently (0.632 → 0.560).  Under the local rule D4 this is exactly the
mechanism of the domain split: prose's next-position survival drops below `k ·` speedup at
depth 4, code's does not before depth 8.

Critic: the reconstruction is *not* unique — only the three cumulative sums are pinned by
the data — so the theorems are stated as realisability (existence) plus a falsifiable
necessary condition, never as identification of the true map.
-/

open SpecDecCPU

open Finset

/-! ## Survival profiles -/

theorem SpecDecCPU.blockMean_antitone{S : ℕ → ℝ} (hS0 : S 0 = 1) (hS : ∀ k, S (k + 1) ≤ S k)
    {d e : ℕ} (hde : d < e) :
    (e - d : ℝ) * (posYield S d - 1) ≥ (d : ℝ) * (posYield S e - posYield S d) := by sorry
