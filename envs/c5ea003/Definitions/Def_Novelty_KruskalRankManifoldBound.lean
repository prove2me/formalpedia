-- Prove2me | Definitions.Def_Novelty_KruskalRankManifoldBound
-- name    : Novelty_KruskalRankManifoldBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:41.377867+00:00
-- url     : https://prove2.me/theorems/a1f1023d-c49b-4d3b-9bf8-0730271cd663
-- title:
--   Aether Catalog definitions — Novelty_KruskalRankManifoldBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KruskalRankManifoldBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KruskalRankManifoldBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_CoverDichotomyCount

/-!
# Kruskal rank of manifold data and the Cover dichotomy bound

The *Kruskal rank* of a finite family of vectors `v : ι → V` is the largest `s`
such that **every** `s` of the vectors are linearly independent — a quantitative
"general position" invariant central to tensor decomposition and compressed
sensing. This file proves the linear-algebra engine behind the mission's claim

  *"`N` points in general position on a `d`-dimensional structure have Kruskal
  rank `s ≤ d + 1`"*

and threads it through Cover's counting function
(`Catalog.Novelty.CoverDichotomy`) to the **manifold-constrained dichotomy
bound** `C_F(N) ≤ C(N, d + M' + 1)`, with strict collapse below `2^N`.

## Main results

* `kruskalRankGe_le_finrank` — the engine: an `s`-family of independent vectors
  forces `s ≤ finrank`;
* `kruskalRank_le_finrank` / `kruskalRank_le_dim_succ` — the packaged invariant
  is bounded by the dimension; on a `(d+1)`-dimensional space it is `≤ d+1`;
* `coverCount_mono_right` — Cover's function is monotone in the parameter budget;
* `manifold_dichotomy_bound` / `manifold_dichotomy_collapse` — the Φ-separable
  dichotomy count is `≤ C(N, d+M'+1)`, and *strictly* below `2^N` once
  `N > d+M'+1`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): the "general position" hypothesis in Cover's theorem
is exactly a *Kruskal rank* statement, and the intrinsic dimension `d` (not the
ambient `M`) caps that rank at `d+1`. Counter-intuitive corollary: enlarging the
ambient space `ℝ^M` around a fixed `d`-manifold cannot increase expressivity —
the bound is `M`-free.

EXPERIMENT (Experimenter): in `ℝ^{d+1}` any `d+2` vectors are dependent
(`finrank`-based), so no configuration attains Kruskal rank `d+2`; verified via
`LinearIndependent.fintype_card_le_finrank`. Cover's function is monotone in its
second slot (`#eval` table, ComputationalEvidence.md), so raising the budget from
`s+M'` to the worst case `d+M'+1` only weakens the bound — safe.

ANALYSIS (Analyst): the crux `kruskalRankGe_le_finrank` needs an *actual*
`s`-element subset to instantiate independence; `Finset.exists_subset_card_eq`
supplies it whenever `s ≤ card ι`. The `sSup` packaging requires the witness
`HasKruskalRankGe v 0` (empty family independent) for non-emptiness of the sup
set. The bridge combines `count_le_coverCount` with monotonicity and the strict
collapse `coverCount_lt_two_pow`.

CRITIQUE (Critic): is `kruskalRank` degenerate (always `0`)? No — the sup set is
downward-closed and contains genuine positive ranks for independent data; the
theorem bounds it *above* by `finrank`, the sharp geometric ceiling. The bridge
is non-vacuous: `coverCountSystem` (from the imported file) is a witnessing
dichotomy system, and the collapse theorem yields the concrete strict inequality
`count < 2^N`.
-- !-- end Lab Notes -- !--
-/

namespace Catalog.Novelty.KruskalRank

open Module Catalog.Novelty.CoverDichotomy

section LinearAlgebra

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype ι]

/-- `HasKruskalRankGe K v s`: every `s`-element subfamily of `v` is linearly
independent. The **Kruskal rank** is the largest such `s`. -/
def HasKruskalRankGe (K : Type*) [Field K] [AddCommGroup V] [Module K V]
    (v : ι → V) (s : ℕ) : Prop :=
  ∀ t : Finset ι, t.card = s → LinearIndependent K (fun i : t => v i)


/-- The **Kruskal rank** of a finite family: the largest size of a "uniformly
independent" subfamily (capped by the number of vectors). -/
noncomputable def kruskalRank (K : Type*) [Field K] [AddCommGroup V] [Module K V]
    (v : ι → V) : ℕ :=
  sSup {s | HasKruskalRankGe K v s ∧ s ≤ Fintype.card ι}




end LinearAlgebra




end Catalog.Novelty.KruskalRank


