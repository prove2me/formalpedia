-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.egf_sum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:00:43.651442+00:00
-- url     : https://prove2.me/submissions/63742519-cb65-4971-a642-363c5cb47d7c

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sum
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 — The combinatorial sum (disjoint union) construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, first admissible construction.
If `A = B + C` is the disjoint union of two combinatorial classes (an object of
size `n` is a `B`-object of size `n` *or* a `C`-object of size `n`), then the
counting sequences add, `Aₙ = Bₙ + Cₙ`, and hence the OGFs add:

  **`(B + C)(z) = B(z) + C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` identity `counts_sum`; the
generating-function identity `ogf_sum` is its image under `ogfSeq`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- Counting sequences add: `(B + C)ₙ = Bₙ + Cₙ`. The genuine combinatorial fact,
from `Fintype.card_sum`. -/
@[simp] lemma CombClass.counts_sum (C D : CombClass) (n : ℕ) :
    (C.sum D).counts n = C.counts n + D.counts n :=
  Fintype.card_sum

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — The labelled sum

Flajolet & Sedgewick, Part A, Chapter II. The combinatorial sum (disjoint union)
is the same construction for labelled and unlabelled classes (it reuses
`CombClass.sum`); only the translation to the EGF differs:

  **`(A + B)(z) = A(z) + B(z)`**.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (A B : CombClass) :
    (A.sum B).egf = A.egf + B.egf := by
  ext n
  rw [map_add, CombClass.coeff_egf, CombClass.coeff_egf, CombClass.coeff_egf,
    CombClass.counts_sum]
  push_cast
  ring
