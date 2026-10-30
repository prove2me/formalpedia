-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_compositions
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_compositions
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:23:32.625253+00:00
-- url     : https://prove2.me/theorems/3ab2b9d3-cb1d-4315-bb6a-64d8ab4e833c
-- title:
--   Formal generating function of integer compositions
-- statement:
--   Let $C(X)$ be the ordinary generating function over $\mathbb{Q}$ of ordered compositions of natural numbers into positive integer parts, including the unique empty composition of zero. As formal power series,
--
--   $$C(X)(1-2X)=1-X.$$
--
--   This expresses the rational generating-function relation for unrestricted integer compositions. The statement is a multiplicative identity in the formal power-series ring.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Compositions.lean#L30. Repository exposition attributes this construction to Flajolet and Sedgewick, Analytic Combinatorics, Part A, Chapter I, §I.3; no independently numbered book theorem is asserted. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.3 — The generating function of integer compositions

Flajolet & Sedgewick, Part A, Chapter I, §I.3. There are `2^{n-1}` compositions
of `n ≥ 1` (Mathlib's `composition_card`), so their ordinary generating function
is

  `C(z) = ∑ₙ 2^{n-1} zⁿ = (1 - z)/(1 - 2z)`,

which we state in polynomial form as `C(z)·(1 - 2z) = 1 - z`. Mathlib has the
counting result but not this generating function, so the identity is new content;
it is the closed form predicted by the symbolic method via `compositions = SEQ(ℙ)`
(see `counts_seq_posInt` in `Sequence.lean`).
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_compositions :
    CombClass.compositions.ogf * (1 - 2 * X) = 1 - X := by sorry
