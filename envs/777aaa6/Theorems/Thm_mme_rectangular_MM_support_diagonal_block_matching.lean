-- Prove2me | Theorems.Thm_mme_rectangular_MM_support_diagonal_block_matching
-- name    : mme_rectangular_MM_support_diagonal_block_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T23:56:32.689187+00:00
-- url     : https://prove2.me/theorems/c2520e8b-0826-4507-9ccb-1bbe1df87f55
-- title:
--   Rectangular matrix-multiplication support matching by diagonal replication
-- statement:
--   Let $H,B,V,W$ be nonnegative integers with $H>0$ and $BH\le V,W$. There is a finite set of triples $E\subseteq[H]\times[V]\times[W]$ that is an induced matching in matrix-multiplication support: each of the three pair-coordinate projections is injective, and three retained edges whose paired coordinates fit together cyclically must be the same edge. Its size satisfies
--
--   $$|E|\ge B H^2\exp\!\bigl(-100\sqrt{\log(H+1)}\bigr).$$
--
--   The larger coordinates can therefore retain multiple disjoint blocks of a square-support matching, rather than truncating both to the smallest side. This is a finite unequal-alphabet building block for matching after directional products have been assembled. The statement does not assume a tensor extraction, and does not yet assert the optimized minimum-of-pair-products bound for arbitrary unordered side lengths.
-- source:
--   Derived finite diagonal-block replication of the square Behrend support matching, Prove2Me theorem mme_MM_support_behrend_induced_matching (Proved777 ID3e41cf76-1a79-4c0d-a7c0-cbdfe2fc5d31). Underlying induced-matching/laser construction: D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp271–272, https://doi.org/10.1016/S0747-7171(08)80013-2. This is an explicitly derived finite combinatorial adapter, not asserted to be a separately numbered source theorem: embed B disjoint diagonal square copies into the two larger alphabets.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

theorem mme_rectangular_MM_support_diagonal_block_matching (H B V W : ℕ) (hH : 0 < H)
    (hV : B * H ≤ V) (hW : B * H ≤ W) :
    ∃ E : Finset (Fin H × Fin V × Fin W),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      (B : ℝ) * (H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by sorry
