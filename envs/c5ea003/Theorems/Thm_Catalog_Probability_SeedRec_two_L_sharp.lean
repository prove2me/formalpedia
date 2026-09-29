-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_two_L_sharp
-- name    : Catalog.Probability.SeedRec.two_L_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:18:06.373743+00:00
-- url     : https://prove2.me/theorems/31c5a046-c428-4a92-9e25-a8e724baed75
-- title:
--   The `2L` certificate is sharp.
-- statement:
--   **The `2L` certificate is sharp.** Two order-`L` registers can agree on
--   `2L - 1` output symbols and disagree at the next one, so no seed-recovery gate
--   based on fewer than `2L` observed symbols is sound.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.two_L_sharp[Nontrivial K] :
--       ∃ c c' σ σ' : Fin L → K,
--         (∀ t < 2 * L - 1, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t) ∧
--           (lfsrPRNG c).stream σ (2 * L - 1) ≠ (lfsrPRNG c').stream σ' (2 * L - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGTwoLSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGTwoLSharpness.lean#L48

-- Thm stub generated from Probability/PRNGTwoLSharpness.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# Sharpness of the `2L` certificate

`lfsr_stream_determined_by_two_L` says that `2L` matching output symbols certify
an order-`L` seed for ever.  This file shows the constant cannot be improved:
for every order `L ≥ 1` and every nontrivial coefficient ring there are two
order-`L` registers whose outputs agree on `2L - 1` symbols and disagree
immediately afterwards.

The witness is the *impulse* seed `σ = (0, …, 0, 1)` run with two tap vectors:

* zero taps — the stream is the single impulse `0^{L-1} 1 0 0 …`;
* the taps `(1, 0, …, 0)`, i.e. the recurrence `y_{t+L} = y_t` — the stream is
  the periodic impulse train `0^{L-1} 1 0^{L-1} 1 …`.

They first differ at time `2L - 1`.

Main statement: `two_L_sharp`.
-/

open Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K] {L : ℕ} [NeZero L]

theorem Catalog.Probability.SeedRec.two_L_sharp[Nontrivial K] :
    ∃ c c' σ σ' : Fin L → K,
      (∀ t < 2 * L - 1, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t) ∧
        (lfsrPRNG c).stream σ (2 * L - 1) ≠ (lfsrPRNG c').stream σ' (2 * L - 1) := by sorry
