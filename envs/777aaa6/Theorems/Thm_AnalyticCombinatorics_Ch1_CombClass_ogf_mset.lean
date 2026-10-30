-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_mset
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_mset
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:19.207652+00:00
-- url     : https://prove2.me/theorems/af66b5c0-cb5c-4cd8-8626-15489d27128d
-- title:
--   Multichoose Euler product for the size-grouped multiset class
-- statement:
--   For a graded class $C$ of finite sets, write $c_n=|C_n|$ and $A_C(z)=\sum_{n\ge0}c_nz^n\in\mathbb Q[[z]]$. For each partition $\lambda$ of $n$ into positive parts, write $r_m(\lambda)$ for the multiplicity of $m$. Define a size-$n$ object to be $\lambda$ together with, for every $0\le m\le n$, a multiset of $C_m$ of cardinality $r_m(\lambda)$. Denote this graded class by $M(C)$. Then
--
--   $$A_{M(C)}(z)=\prod_{m\ge1}\left(\sum_{k\ge0}\operatorname{multichoose}(c_m,k)z^{mk}\right).$$
--
--   Here $\operatorname{multichoose}(c,k)$ counts size-$k$ multisets from a $c$-element set, including the usual zero-cardinality cases. Partition parts are positive, so $r_0(\lambda)=0$: this source model ignores zero-size decorations even if $C_0$ is nonempty. The theorem has no hypothesis $C_0=\varnothing$; its interpretation as unrestricted finite multisets of arbitrary $C$-objects requires that additional model condition. All infinite operations are coefficientwise formal ones with discrete rational coefficients.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Mset.lean#L83. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Mset
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 — The multiset construction MSET(C): counts layer

Flajolet & Sedgewick, Part A, Chapter I, §I.2. `MSET(C)` forms finite multisets of
C-objects (`C₀=∅`). Grouping a multiset by object size, a size-`n` object is a
partition `p` of `n` (recording the multiplicities of each size) together with, for
each size `m`, a size-`(mult m)` multiset of the `Cₘ` objects of that size (a `Sym`).

This file builds the graded `Fintype` model and the counting identity, and connects
it to Mathlib's `Nat.Partition.genFun`:

  `MSET(C)ₙ = ∑_{p:Partition n} ∏_m multichoose(Cₘ, mult_m p)
            = genFun (fun m j => multichoose(Cₘ, j)) |>.coeff n`.

The Euler product OGF `∏_m (1 - z^m)^{-Cₘ}` is proved in the OGF layer. (For `C = ℙ`,
`multichoose 1 k = 1`, recovering the partition flagship.)
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatMset

local instance _root_.AnalyticCombinatorics.Ch1.instDiscRatMset : DiscreteTopology ℚ := ⟨rfl⟩

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_mset (C : CombClass) :
    C.mset.ogf
      = ∏' i, ∑' k, ((C.counts (i + 1)).multichoose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k) := by sorry
