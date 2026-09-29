-- Prove2me | Theorems.Thm_Hadwiger_completeMinor_three_C6
-- name    : Hadwiger.completeMinor_three_C6
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:42:23.057814+00:00
-- url     : https://prove2.me/theorems/1edf641e-f9c8-4a84-97cc-a7f4bd62860d
-- title:
--   Contracting the three pairs `{0,1}`, `{2,3}`, `{4,5}` turns `C₆` into a
-- statement:
--   Contracting the three pairs `{0,1}`, `{2,3}`, `{4,5}` turns `C₆` into a
--   triangle: `K₃` is a minor of `C₆`.
--
--   ```lean
--   theorem Hadwiger.completeMinor_three_C6: CompleteMinor 3 C6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerConverse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerConverse.lean#L59

-- Thm stub generated from Probability/HadwigerConverse.lean
import Mathlib
import Definitions.Def_Probability_HadwigerConverse
import Definitions.Def_Probability_HadwigerK3
/-
  The Converse of Hadwiger's Conjecture is False
  ==============================================

  Hadwiger's conjecture says `χ(G) ≥ k+1 ⟹ K_{k+1} ≼ G`.  A natural — and
  frequently conjectured — strengthening is that the two conditions are
  *equivalent*, i.e. that the chromatic number is **minor-monotone**:
  `H ≼ G ⟹ χ(H) ≤ χ(G)`.  This file refutes that with an explicit
  counterexample: the `6`-cycle is bipartite yet contracts onto a triangle.

  Main results:

  * `Hadwiger.C6_colorable_two`            : `C₆` is `2`-colourable.
  * `Hadwiger.completeMinor_three_C6`      : `K₃` is a minor of `C₆`
                                             (branch sets `{0,1}, {2,3}, {4,5}`).
  * `Hadwiger.chromaticNumber_not_minorMonotone` : the chromatic number is **not**
                                             minor-monotone.
  * `Hadwiger.converse_hadwiger_false`     : consequently the converse of
                                             Hadwiger's implication fails for
                                             `k = 2` (and hence the conjecture
                                             cannot be upgraded to an
                                             equivalence).

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): contraction can *raise* the chromatic number, so
    the Hadwiger implication is strictly one-directional.
  Experiment (Experimenter): the smallest witness is the `6`-cycle: pairing up
    consecutive vertices `{0,1}, {2,3}, {4,5}` gives three connected, pairwise
    disjoint sets joined by the edges `1–2`, `3–4`, `5–0`, hence a `K₃` model,
    while the parity colouring shows `χ(C₆) = 2`.
  Analysis (Analyst): the phenomenon is exactly the failure of *odd* structure to
    be preserved under contraction — a bipartite graph can contract onto an odd
    cycle whenever it contains a cycle of length `≥ 4`.
  Critique (Critic): the witness must be checked to really be `C₆`
    (`SimpleGraph.cycleGraph 6`) and the colouring must be verified on all `36`
    ordered pairs; both are done by `decide` inside the proofs, but the
    surrounding statements are non-trivial mathematical claims.
  Synthesis (PI): Hadwiger's conjecture is an implication, never an equivalence;
    minor-closed classes therefore give upper bounds on `χ` only through the
    *excluded* minor, never through a contracted witness.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

theorem Hadwiger.completeMinor_three_C6: CompleteMinor 3 C6 := by sorry
