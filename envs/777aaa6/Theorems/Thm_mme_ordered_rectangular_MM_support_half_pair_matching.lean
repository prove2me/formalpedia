-- Prove2me | Theorems.Thm_mme_ordered_rectangular_MM_support_half_pair_matching
-- name    : mme_ordered_rectangular_MM_support_half_pair_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:00:34.869024+00:00
-- url     : https://prove2.me/theorems/f5847054-606d-454b-8019-589f2c943b90
-- title:
--   Ordered rectangular support retains half the smallest pair product up to Behrend loss
-- statement:
--   Let $H,V,W$ be integers with $0<H\le V\le W$. There is an induced matching $E\subseteq[H]\times[V]\times[W]$ in matrix-multiplication support, with all three pair-coordinate projections injective, such that
--
--   $$|E|\ge \frac{HV}{2}\exp\!\bigl(-100\sqrt{\log(H+1)}\bigr).$$
--
--   Under the stated ordering, $HV=\min(HV,HW,VW)$ is the smallest pair-coordinate capacity. Thus this finite matching retains that capacity up to a constant factor and the inherited subexponential loss, rather than reducing both larger coordinates to $H$.
--
--   The inducedness condition excludes every mixed cyclic support triple formed from distinct retained edges. This is an actual finite support construction, not an assumed tensor-value bound. Permuting arbitrary unordered side lengths and realizing the matching in a product grading are separate interfaces.
-- source:
--   Derived ordered-side consequence of the finite diagonal-block replication of square Behrend support matching (mme_rectangular_MM_support_diagonal_block_matching), using B=floor(V/H). Underlying square induced-matching/laser construction: D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp271–272, https://doi.org/10.1016/S0747-7171(08)80013-2; Prove2Me square support theorem mme_MM_support_behrend_induced_matching, Proved777 ID3e41cf76-1a79-4c0d-a7c0-cbdfe2fc5d31. This is an explicitly derived finite adapter, not a separately numbered source theorem. The only new estimate is V<=2H floor(V/H) under H<=V.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

theorem mme_ordered_rectangular_MM_support_half_pair_matching (H V W : ℕ) (hH : 0 < H) (hHV : H ≤ V) (hVW : V ≤ W) :
    ∃ E : Finset (Fin H × Fin V × Fin W),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      ((H : ℝ) * (V : ℝ) / 2) *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by sorry
