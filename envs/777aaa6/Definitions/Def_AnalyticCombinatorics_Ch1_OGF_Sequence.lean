-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
-- name    : AnalyticCombinatorics_Ch1_OGF_Sequence
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:21:37.566947+00:00
-- url     : https://prove2.me/theorems/798bbb6e-1b67-4338-92bd-81b682116baa
-- title:
--   Ordered positive-size component sequences and integer compositions
-- statement:
--   Let $C$ be a combinatorial class, with $C_n$ its finite set of size-$n$ objects. A sequence object of total size $n$ is an ordered composition $(n_1,\ldots,n_k)$ of $n$ into positive integers, together with a selected object from each set $C_{n_i}$. Equivalently, its object type is represented by
--
--   $$\coprod_{(n_1,\ldots,n_k)\vDash n}\prod_{i=1}^k C_{n_i}.$$
--
--   The empty composition gives the empty sequence at size zero. This represents unrestricted finite sequences of $C$-objects when $C$ has no size-zero objects. The foundation also provides the class with one object of every positive size and the class of integer compositions themselves. These definitions connect finite combinatorial objects with their counting and generating-function identities.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Sequence.lean. Definitions for the sequence-construction portion of Flajolet and Sedgewick, Analytic Combinatorics (Cambridge University Press, 2009), Chapter I. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The sequence construction `SEQ(C)` (F&S §I.2): a size-`n` object is a
composition `c` of `n` together with a choice of a `C`-object for each (positive)
part. Faithful to `SEQ(C)` exactly when `C` has no size-`0` object. -/
def CombClass.seq (C : CombClass) : CombClass where
  Obj n := Σ c : Composition n, ∀ i : Fin c.length, C.Obj (c.blocksFun i)
  finObj _ := inferInstance

/-- The class `ℙ` of positive integers: one object of each size `n ≥ 1`
(F&S §I.3, the parts of a composition). -/
def CombClass.posInt : CombClass where
  Obj n := Fin (if 0 < n then 1 else 0)
  finObj _ := inferInstance

/-- The class of integer compositions (F&S §I.3): a size-`n` object is a
composition of `n`. This is Mathlib's `Composition n`. -/
def CombClass.compositions : CombClass where
  Obj n := Composition n
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


