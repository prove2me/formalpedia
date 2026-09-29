-- Prove2me | Theorems.Thm_mme_complete_split_exact_type_subexponential_repair_budget
-- name    : mme_complete_split_exact_type_subexponential_repair_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:57:20.253516+00:00
-- url     : https://prove2.me/theorems/0685eb04-9610-4578-ac64-58085acbd03c
-- title:
--   Exact complete-profile cardinalities and a subexponential eight-way repair-copy budget
-- statement:
--   Fix a level $\ell$. Using natural-number truncated subtraction in $\ell-1$, a complete fine word at this level has $c=2^{\ell-1}$ positions, each with alphabet $\{0,1,2\}$. For every chunk count $N$ and every triple of exact complete-split profiles, let $B_i$ be the set of full-label words whose empirical distribution is exactly profile $i$. Then
--
--   $$
--   \prod_{i=0}^2 |B_i| \le 3^{3cN}.
--   $$
--
--   Moreover, for every real $\delta>0$, for all sufficiently large natural $N$ there is a natural depth $h$, independent of the three profiles, such that every such triple satisfies
--
--   $$
--   \prod_{i=0}^2 |B_i| < (2N)^h,
--   \qquad
--   \log(8^h)<\delta N.
--   $$
--
--   This supplies an arbitrarily small exponential copy cost for the finite three-mode repair with $d=2N$: its depth threshold holds and its actual number of copies is $8^h$. The logarithm is natural. The count $N$ measures complete level-$\ell$ factors, not individual fine positions; at level 2 the universal three-mode bound is $729^N$, not $27^N$. Empty exact types are allowed. No tensor extraction, small-hole condition, positive-tolerance uniformity, or numerical feasibility is assumed or proved by this scalar theorem.
-- source:
--   Derived scalar overhead interface for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definition 4.1 and Theorem 4.2; the exact-domain chunk-shuffle repair is explained in Vassilevska Williams, Xu, Xu, Zhou, https://arxiv.org/abs/2307.07970v2, proof of restated Corollary 4.2, pp. 48–49. Uses the actual public CompleteWord and ApproxConsistent definitions. The ceiling choice h=ceil(delta*N/(2*log 8)) is a derived implementation of the subexponential overhead argument, not a quoted formula or a replacement for finite tensor repair.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter MME MME.CompleteSplit MME.DWZComponentRestriction
open scoped BigOperators Classical

set_option autoImplicit false

theorem mme_complete_split_exact_type_subexponential_repair_budget (ell : ℕ) :
    (∀ (N : ℕ) (beta : Fin 3 → Profile ell),
      (∏ i : Fin 3,
        Fintype.card {w : PowIndex (CompleteWord ell) N //
          ApproxConsistent id (beta i) 0 w}) ≤
        3 ^ (3 * (2 ^ (ell - 1)) * N)) ∧
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      ∃ h : ℕ,
        (∀ beta : Fin 3 → Profile ell,
          (∏ i : Fin 3,
            Fintype.card {w : PowIndex (CompleteWord ell) N //
              ApproxConsistent id (beta i) 0 w}) < (2 * N) ^ h) ∧
        Real.log ((8 ^ h : ℕ) : ℝ) < delta * N := by sorry
