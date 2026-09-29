-- Prove2me | Theorems.Thm_mme_subrankCapacityPoly_ge_of_witnesses
-- name    : mme_subrankCapacityPoly_ge_of_witnesses
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-01T16:23:20.295746+00:00
-- url     : https://prove2.me/theorems/37b73264-e88d-4fb1-a408-803e4e3c043e
-- statement:
--   Abstract bridge: per-$(N, \varepsilon)$ polynomial-bounded witnesses force the value into $\mathrm{subrankCapacityPoly}$. If a real number $V \ge 1$ admits the polynomial-witness construction defining $\mathrm{subrankCapacityPoly}\,T$ -- i.e., there is $c : \mathbb{R}$ such that for every $\varepsilon > 0$, frequently many $N$ exhibit $(k, a, b, c')$ with $k \le (N+1)^c$, a $\mathrm{Restrict}$ into $T^{\otimes N}$, and H\"older lower bound $V^N (1-\varepsilon) \le \sum_i (a_i b_i c'_i)^{1/3}$ -- then $V \le \mathrm{subrankCapacityPoly}\,T$. This is the paper-agnostic sSup-bridge: identical statement works for any $\omega$-bound construction (Strassen, CW, Stothers, Vassilevska Williams, Le Gall, Alman--Vassilevska Williams). The proof requires a $\mathrm{BddAbove}$ analysis of the defining set of $\mathrm{subrankCapacityPoly}\,T$ plus a standard $\mathrm{le\_csSup}$ application.
-- source:
--   Strassen asymptotic spectrum framework; abstract sSup-le-of-mem bridge

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_mme_subrank_capacity_poly
import Definitions.Def_mme_tensor_rank

open MME BigOperators Filter

universe u

/-- **Abstract bridge: per-(N, ε) polynomial-bounded witnesses force the
value into `subrankCapacityPoly`.**

If a real number `V ≥ 1` admits the *polynomial-witness* construction
defining `subrankCapacityPoly T` — i.e., there is `c : ℝ` such that for
every `ε > 0`, frequently many `N` exhibit `(k, a, b, c')` with
`k ≤ (N+1)^c`, a `Restrict` into `T^{⊗N}`, and Hölder lower bound
`V^N · (1 - ε) ≤ ∑ᵢ (aᵢ·bᵢ·c'ᵢ)^{1/3}` — then `V ≤ subrankCapacityPoly T`.

This is the **paper-agnostic** abstract `sSup`-le-of-mem bridge. It
says: membership in the defining set of `subrankCapacityPoly T` yields
the asymptotic-value inequality, modulo the standard bounded-above /
nonemptiness analysis required by `Real.sSup`.

**Reusability.** Identical statement works for any ω-bound construction
(Strassen, CW, Stothers, Vassilevska Williams, Le Gall, Alman–Vassilevska
Williams) — every such construction unwraps to a per-N polynomial witness;
this lemma converts that into the supremum bound in one step.

**Status.** Open. The interior of the proof requires:
* a `BddAbove` analysis of the defining set of `subrankCapacityPoly T`
  (typically a uniform `dim(T)^N`-style bound on each block-sum or on the
  Strassen rank of `T^{⊗N}`), and
* `le_csSup` for the supremum.

Both pieces are abstract and reusable; isolating them here keeps the
paper-specific analytic-combinatorial content out of the bridge. -/
theorem mme_subrankCapacityPoly_ge_of_witnesses
    {K : Type u} [Field K] (T : TensorObj K 3)
    (V : ℝ) (hV : 1 ≤ V)
    (hwit : ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            (T.kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) :
    V ≤ subrankCapacityPoly T := by
  sorry
