-- Prove2me | solution 1 for RademacherWigner.filter_edge_walk6
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:50.140532+00:00
-- url     : https://prove2.me/submissions/3ef68bab-f952-4584-980b-aae5e8e1725d

-- Sol generated from Probability/WignerWalkParity.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The sign-flip involution at arbitrary order: parity of edge multiplicities

`Probability.WignerRademacherEnsemble` kills the expectation of a closed **4**-walk
whose first edge is traversed exactly once, by flipping the Rademacher variable
attached to that edge.  This file isolates the mechanism and proves it at
**arbitrary order**, for an arbitrary walk of arbitrary length:

* `RademacherWigner.prod_entry_flipEdge` — flipping the sign of one edge `p`
  multiplies the product of matrix entries along a walk by `(-1)^c`, where `c` is
  the number of steps of the walk that traverse `p`;
* `RademacherWigner.expect_prod_entry_eq_zero` — hence, if some edge is traversed
  an **odd** number of times, the ensemble average of the walk monomial is `0`.

This is the exact combinatorial reason why only walks whose edge multiset has all
multiplicities even survive in `E [ tr W^m ]`, which is the input to the
moment-method proof of the semicircle law at every order.  Two instantiations are
given: the length-four case, which reproves
`RademacherWigner.expect_term_eq_zero`, and the length-six case, which is the first
case not covered by the earlier files (and the first step towards the exact sixth
trace moment).
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}

/-! ### Edge multiplicities along a walk -/






/-! ### The closed four-walk, revisited -/





/-! ### The closed six-walk -/






open RademacherWigner in
theorem solution{i j k l m n : Fin N}
    (e2 : edgeOf j k ≠ edgeOf i j) (e3 : edgeOf k l ≠ edgeOf i j)
    (e4 : edgeOf l m ≠ edgeOf i j) (e5 : edgeOf m n ≠ edgeOf i j)
    (e6 : edgeOf n i ≠ edgeOf i j) :
    ((Finset.range 6).filter fun t =>
        edgeOf (walk6 i j k l m n t) (walk6 i j k l m n (t + 1)) = edgeOf i j) = {0} := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, hedge⟩
    interval_cases t
    · rfl
    · exact absurd (by simpa [walk6] using hedge) e2
    · exact absurd (by simpa [walk6] using hedge) e3
    · exact absurd (by simpa [walk6] using hedge) e4
    · exact absurd (by simpa [walk6] using hedge) e5
    · exact absurd (by simpa [walk6] using hedge) e6
  · rintro rfl
    exact ⟨by norm_num, by simp [walk6]⟩
