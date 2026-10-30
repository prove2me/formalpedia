-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_pset
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_pset
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:18.154667+00:00
-- url     : https://prove2.me/theorems/0c4f8f1a-0026-4cc6-8ed2-0e1ce6194f12
-- title:
--   Binomial Euler product for the size-grouped subset class
-- statement:
--   For a graded class $C$ of finite sets, write $c_n=|C_n|$ and $A_C(z)=\sum_{n\ge0}c_nz^n\in\mathbb Q[[z]]$. For each partition $\lambda$ of $n$ into positive parts, write $r_m(\lambda)$ for the multiplicity of $m$. Define a size-$n$ object to be $\lambda$ together with, for every $0\le m\le n$, a subset of $C_m$ of cardinality $r_m(\lambda)$. Denote this graded class by $S(C)$. Then
--
--   $$A_{S(C)}(z)=\prod_{m\ge1}\left(\sum_{k\ge0}\binom{c_m}{k}z^{mk}\right).$$
--
--   Partition parts are positive, so $r_0(\lambda)=0$: this source model ignores zero-size decorations even if $C_0$ is nonempty. The theorem has no hypothesis $C_0=\varnothing$; its interpretation as unrestricted finite sets of arbitrary $C$-objects requires that additional model condition. All infinite operations are coefficientwise formal ones with discrete rational coefficients.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Pset.lean#L82. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pset
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 — The powerset construction PSET(C)

Flajolet & Sedgewick, Part A, Chapter I, §I.2. `PSET(C)` forms finite *sets* of
C-objects (each object used at most once, `C₀=∅`). Grouping a set by object size, a
size-`n` object is a partition `p` of `n` together with, for each size `m`, a
*subset* of card `(mult m)` of the `Cₘ` objects of that size. The number of size-`k`
subsets of a `c`-set is `choose(c,k)`, so

  `PSET(C)ₙ = ∑_{p:Partition n} ∏_m choose(Cₘ, mult_m p)
            = genFun (fun m j => choose(Cₘ, j)) |>.coeff n`,

and the OGF is `PSET(C)(z) = ∏_{m≥1} (1 + z^m)^{Cₘ}` (since `∑_k choose(c,k) x^k =
(1+x)^c`). The construction mirrors `MSET` with subsets/`choose` in place of
multisets/`multichoose`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatPset

local instance _root_.AnalyticCombinatorics.Ch1.instDiscRatPset : DiscreteTopology ℚ := ⟨rfl⟩

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_pset (C : CombClass) :
    C.pset.ogf
      = ∏' i, ∑' k, ((C.counts (i + 1)).choose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k) := by sorry
