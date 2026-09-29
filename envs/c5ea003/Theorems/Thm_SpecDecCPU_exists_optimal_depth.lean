-- Prove2me | Theorems.Thm_SpecDecCPU_exists_optimal_depth
-- name    : SpecDecCPU.exists_optimal_depth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:52:52.375479+00:00
-- url     : https://prove2.me/theorems/831598c1-7844-4a07-8ad0-da1cdb3eb36e
-- title:
--   Every (acceptance, cost) pair has a throughput-optimal draft depth.
-- statement:
--   Every (acceptance, cost) pair has a throughput-optimal draft depth.
--
--   ```lean
--   theorem SpecDecCPU.exists_optimal_depth{a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 < c) :
--       ∃ D : ℕ, ∀ d : ℕ, speedup a c d ≤ speedup a c D := by sorry
--   /-! ## Comparative statics: the depth frontier is monotone in acceptance -/
--
--
--
--
--
--
--
--
--   /-! ## The mean-yield reading and the CPU verification overhead -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SpeculativeDecodingCostDominance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SpeculativeDecodingCostDominance.lean#L369

-- Thm stub generated from Shared/SpeculativeDecodingCostDominance.lean
import Mathlib
import Definitions.Def_Shared_SpeculativeDecodingCostDominance

/-!
# Draft-cost dominance and domain-parameterised depth in CPU speculative decoding

This file develops a model-free theory of the object measured in the NET-91 experiment:
the throughput of *speculative decoding* of a large target model by a small draft model,
when everything runs on a CPU, so that the draft's `d` sequential proposal steps are paid
in full and only the verification pass amortises.

## The block model

A speculative *block* consists of `d` sequential draft steps followed by one verification
pass of the target.  Measuring time in units of one target decode step:

* `blockCost c d = 1 + c * d` — one verification pass plus `d` draft steps of relative
  cost `c` each (`c ≈ 0.118` for the 0.5B draft, `c ≈ 0.234` for the 1.5B draft against
  the 7B target);
* `yieldGeom a d = ∑_{i ≤ d} a ^ i` — the expected number of target tokens committed by
  the block when each drafted position is accepted independently with probability `a`
  (the classical Leviathan-style yield: the bonus token plus the accepted prefix);
* `speedup a c d = yieldGeom a d / blockCost c d` — tokens per unit target-step, i.e. the
  speedup over greedy autoregressive decoding, whose value is `speedup a c 0 = 1`.

## What is proved

* **Exact comparison criterion** (`speedup_lt_speedup_iff`) and the *cheap-draft law at
  equal acceptance* (`cheaper_draft_wins`).
* **Cost dominance, all six measured head-to-heads** (`cost_dominance_all_six`): feeding
  the *measured* acceptance rates and the *measured* relative draft costs into the model,
  the 0.5B draft beats the 1.5B draft in every one of the six (domain × depth) cells —
  including `code, d = 8`, where the 1.5B accepts strictly more (60.3% vs 56.0%).
* **Asymptotic form of the law** (`asymptotic_cost_dominance`): `d · speedup → 1/(c(1-a))`
  (`tendsto_d_speedup`), so the invariant that ranks two drafts at large depth is the
  product `c * (1 - a)`; an acceptance advantage must beat the cost ratio *multiplicatively
  in the rejection rate*.  For the measured pair, `0.118·0.44 = 0.0519 < 0.234·0.397 =
  0.0929`, and the 1.5B draft would need acceptance `≥ 77.8%` at `d = 8` to overturn it
  (`crossover_acceptance_needed`).
* **Depth collapse** (`speedup_lt_one_of_deep`, `exists_depth_collapse`): for every `a < 1`
  and `c > 0` deep enough drafting is a *net loss*, with the explicit gate
  `(1 - a) * blockCost c d > 1`.  Instantiated: prose at `d = 8` is a predicted loss for
  both drafts (`prose_depth8_loss_small`, `prose_depth8_loss_large`) while code at `d = 8`
  is a predicted win for the small draft (`code_depth8_win_small`).
* **Existence of an optimal depth** (`exists_optimal_depth`).
* **Comparative statics — the depth frontier is monotone in acceptance**
  (`deepenPays_mono_acceptance`, `depth_frontier_monotone`): if deepening from `d` to `e`
  pays at acceptance `a`, it pays at every `a' ≥ a`.  This is the formal content of
  "optimal depth is domain-parameterised": code accepts more, hence its optimal depth is
  never below prose's.
* **An informative failure** (`iid_cannot_explain_code_depth8`): the same comparative
  statics *falsifies* the i.i.d. reading of the measured acceptance numbers.  For every
  per-position acceptance `a ≤ 0.8` the model ranks `d = 4` strictly above `d = 8` at the
  0.5B draft cost; the measured code acceptance is 56%, yet `d = 8` measured faster.  So
  the reported percentage cannot be a per-position independent acceptance probability.
* **The repaired reading and a derived hardware prediction**: under the *mean-yield*
  reading `meanYield q d = 1 + q * d` the code cells are reproduced
  (`mean_reading_matches_code`), but an affine yield over an affine cost is monotone in
  depth (`affine_ratio_mono`, `affine_ratio_anti`), so it can never produce an interior
  optimum, and reproducing the prose `d = 8` loss forces extra per-position verification
  cost.  Quantitatively (`verification_overhead_bracket`) the marginal CPU cost of one
  extra verified position lies strictly between `0.191` and `0.442` target-steps: on a
  CPU, verification does **not** amortise the way GPU folklore assumes.

-- !-- Lab Notes -- !--
Hypothesizer (7 conjectures, ranked by expected impact):
 (H1) [BOLD] There is a single scalar invariant `c * (1 - a)` that ranks two drafts at
      large depth; acceptance and cost are not independently meaningful.
 (H2) [BOLD] Optimal depth is a monotone comparative static of acceptance: the whole
      "deepening pays" frontier is upward closed in `a`, so the code/prose depth split is
      forced, not incidental.
 (H3) Deep drafting is always eventually a net loss, with a closed-form gate.
 (H4) The cheap draft wins every measured head-to-head *inside the model*, i.e. the
      refutation of P3 is a theorem about the model, not only an observation.
 (H5) [BOLD] The reported acceptance percentages are not per-position probabilities; the
      i.i.d. model with those numbers is falsified by the code `d = 8` cell.
 (H6) A mean-yield (affine) reading fixes the code cells but cannot have an interior
      optimum, hence cannot alone explain the prose collapse.
 (H7) Combining H5 and H6 yields a two-sided numerical bracket on the CPU verification
      overhead — a prediction testable in the next round.

Experimenter: H1–H7 are all formalised below with zero sorries.  The measured NET-91
inputs (Qwen2.5-7B-Instruct Q4_K_M target, i9-9900K, threads = 8, 5.79 tok/s baseline)

  draft   depth   prose accept   prose speedup   code accept   code speedup
  0.5B      2        63.9%          1.254x          71.6%         1.352x
  0.5B      4        47.7%          1.416x          63.0%         1.616x
  0.5B      8        30.9%          0.979x          56.0%         1.661x
  1.5B      2        63.2%          1.016x          83.4%         1.195x
  1.5B      4        51.9%          1.153x          74.8%         1.395x
  1.5B      8        44.9%          0.982x          60.3%         1.354x

with relative draft costs 0.118 and 0.234, enter only as *numerals inside statements*,
never as axioms.

Analyst: fed the measured acceptances, the block model reproduces the sign (win/loss) of
11 of the 12 measured cells and the winner of all 6 head-to-heads.  The single sign
failure is exactly the cell the falsification theorem isolates (1.5B, code, `d = 8`), and
its cause is structural, not numerical: under i.i.d. acceptance no `a ≤ 0.8` makes `d = 8`
beat `d = 4` at these costs.  Hence "true but with a different definition": the measured
percentage is a *mean accepted fraction*, not a per-position probability, and the two
readings are provably inequivalent here.

Critic: the numeric cells are `norm_num` evaluations, so each is stated only as a
corollary of a structural lemma (`speedup_lt_speedup_iff`, `speedup_lt_one_of_deep`,
`deepenPays_mono_acceptance`), never as the headline result; the headline results are the
quantified laws.  No theorem below is `True`, definitional, or `native_decide`.
-/

open SpecDecCPU

open Finset Filter Topology

/-! ## The block model -/
















/-! ## Comparison criterion and the cheap-draft law -/



/-! ### The six measured head-to-heads

In each cell the 0.5B draft (relative cost `0.118`) is compared with the 1.5B draft
(relative cost `0.234`) at the *measured* acceptance rates. -/








/-! ## The asymptotic invariant `c * (1 - a)` -/






/-! ## Depth collapse: deep drafting is eventually a net loss -/







/-! ## Existence of an optimal depth -/

theorem SpecDecCPU.exists_optimal_depth{a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 < c) :
    ∃ D : ℕ, ∀ d : ℕ, speedup a c d ≤ speedup a c D := by sorry
