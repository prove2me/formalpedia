-- Prove2me | Theorems.Thm_mme_rectangular_MM_support_min_pair_matching
-- name    : mme_rectangular_MM_support_min_pair_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:06:47.909747+00:00
-- url     : https://prove2.me/theorems/ac5ca90b-1b65-4c65-b589-7bd380765458
-- title:
--   Arbitrary rectangular support retains half the minimum pair capacity up to Behrend loss
-- statement:
--   Let $H,V,W$ be positive integers and set $s=\min(H,V,W)$. There is a finite induced matching $E\subseteq[H]\times[V]\times[W]$ in matrix-multiplication support satisfying
--
--   $$|E|\ge\frac{\min(HV,HW,VW)}{2}\exp\!\bigl(-100\sqrt{\log(s+1)}\bigr).$$
--
--   All three pair-coordinate projections of $E$ are injective. Moreover, three retained edges whose paired coordinates fit together cyclically must coincide, so the result supplies the actual support needed for coordinate zeroing, not merely a cardinality bound.
--
--   No ordering of the three side lengths is assumed. This finite result permits directional alphabet products to be formed before taking their smallest pair capacity. It does not assert that those alphabet products have yet been realized by a tensor grading or settle any matrix-multiplication exponent.
-- source:
--   Derived coordinate-permutation closure of the ordered rectangular support construction mme_ordered_rectangular_MM_support_half_pair_matching and its diagonal replication helper. Underlying square Behrend support/laser construction: D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp271–272, https://doi.org/10.1016/S0747-7171(08)80013-2; Prove2Me square support theorem mme_MM_support_behrend_induced_matching, Proved777 ID3e41cf76-1a79-4c0d-a7c0-cbdfe2fc5d31. This is an explicitly derived finite adapter, not a separately numbered source theorem. The proof transports the actual edge set through coordinate swaps/rotations with exact cardinality preservation, then treats all six orders.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

theorem mme_rectangular_MM_support_min_pair_matching (H V W : ℕ) (hH : 0 < H) (hV : 0 < V) (hW : 0 < W) :
    ∃ E : Finset (Fin H × Fin V × Fin W),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      (((min (H * V) (min (H * W) (V * W)) : ℕ) : ℝ) / 2) *
          Real.exp (-100 * Real.sqrt
            (Real.log (((min H (min V W) + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by sorry
