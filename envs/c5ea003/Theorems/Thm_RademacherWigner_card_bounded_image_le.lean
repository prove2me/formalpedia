-- Prove2me | Theorems.Thm_RademacherWigner_card_bounded_image_le
-- name    : RademacherWigner.card_bounded_image_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:00:32.453626+00:00
-- url     : https://prove2.me/theorems/d79f7a39-373d-4e79-8426-4830e49ee169
-- title:
--   A function `Fin n → Fin N` whose image has at most `r ≤ N` elements is encoded by
-- statement:
--   A function `Fin n → Fin N` whose image has at most `r ≤ N` elements is encoded by
--   an `r`-element subset of `Fin N` together with a map into it; hence there are at most
--   `N ^ r · r ^ n` of them.
--
--   ```lean
--   theorem RademacherWigner.card_bounded_image_le{n r : ℕ} (hr : r ≤ N) :
--       ((univ : Finset (Fin n → Fin N)).filter
--           (fun u => (Finset.image u univ).card ≤ r)).card ≤ N ^ r * r ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerMomentGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerMomentGrowth.lean#L141

-- Thm stub generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Polynomial growth of every even moment: tightness of the empirical spectral law

`Probability.WignerAllOrderParity` reduces the computation of every trace moment of
the symmetric Rademacher ensemble to a count of *even closed walks* — loop-free
closed walks all of whose edge multiplicities are even — and proves that the odd
moments vanish identically.  This file supplies the missing quantitative half at
even order: an even closed walk of length `2k` can visit at most `k + 1` distinct
vertices, so there are at most `N^(k+1) (k+1)^(2k)` of them and

  `E [ tr (W ^ (2k)) ] ≤ N^(k+1) · (k+1)^(2k)`,
  `E [ (1/N) tr ((W/√N) ^ (2k)) ] ≤ (k+1)^(2k)`   (uniformly in `N`).

The structural core is graph-theoretic and is proved from scratch here:

* `RademacherWigner.card_visited_le` — along any walk, the number of vertices
  visited never exceeds `1 +` the number of distinct edges used (a spanning-tree
  bound, proved by induction on the length of the walk);
* `RademacherWigner.card_edgesUsed_le` — if every edge multiplicity is even, then
  twice the number of distinct edges is at most the length of the walk;
* `RademacherWigner.card_visited_le_of_even` — combining the two, an even closed
  walk of `2k` steps visits at most `k + 1` vertices;
* `RademacherWigner.card_bounded_image_le` — a function `Fin n → Fin N` whose image
  has at most `r` elements is determined by an `r`-element subset together with a
  map into it, giving at most `N^r · r^n` such functions.

Uniform boundedness of all normalised moments is exactly the tightness input of the
moment method: together with `expect_trace_pow_odd` it says that the expected
empirical spectral distribution of `W/√N` has moments that neither blow up nor
oscillate with `N`, at *every* order.
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}

/-! ### Vertices and edges visited by a walk -/










/-! ### Counting functions with a small image -/

theorem RademacherWigner.card_bounded_image_le{n r : ℕ} (hr : r ≤ N) :
    ((univ : Finset (Fin n → Fin N)).filter
        (fun u => (Finset.image u univ).card ≤ r)).card ≤ N ^ r * r ^ n := by sorry
