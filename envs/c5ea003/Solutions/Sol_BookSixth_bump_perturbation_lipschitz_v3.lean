-- Prove2me | solution 1 for BookSixth.bump_perturbation_lipschitz_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T01:58:52.002124+00:00
-- url     : https://prove2.me/submissions/a21cff58-b385-44f3-9c33-84eb41752ef6

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

-- # A finite bump perturbation is Lipschitz with constant `M + (K + 1) * L` per summand
--
-- For `d i z = S i z - z` and `c i = chi i`, write `F z = ∑ i, c i z • d i z`.
-- The key identity, valid in any module, is
--
-- ```
-- c x • d x - c y • d y = (c x - c y) • d x + c y • (d x - d y)
-- ```
--
-- The first product is controlled by `1`-Lipschitzness of `chi i` together with
-- `‖S i x - x‖ ≤ M`, giving `M * ‖x - y‖`.  The second is controlled by
-- `‖chi i y‖ ≤ L` together with
-- `d x - d y = (S i x - S i y) - (x - y)`, whose norm is at most `(K + 1) * ‖x - y‖`
-- because `S i` is `K`-Lipschitz.  Setting `K = 1` recovers the constant
-- `2 * L + M` of the accepted `bump_perturbation_lipschitz_v2`.

theorem solution
    (n : ℕ) (K L M : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 1 ≤ K)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, LipschitzWith 1 (chi i))
    (hchiL : ∀ i x, ‖chi i x‖ ≤ L)
    (hS : ∀ i, LipschitzWith (Real.toNNReal K) (S i))
    (hSiy : ∀ i y, ‖S i y - y‖ ≤ M) :
    ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖
        ≤ (∑ i : Fin n, (M + (K + 1) * L)) * ‖x - y‖ := by
  intro x y
  -- The per-summand estimate, with the constant `M + (K + 1) * L`.
  have hper : ∀ i, ‖chi i x • (S i x - x) - chi i y • (S i y - y)‖
      ≤ (M + (K + 1) * L) * ‖x - y‖ := by
    intro i
    -- The exact vector identity, proved once and used by `rw` below.
    have hid : chi i x • (S i x - x) - chi i y • (S i y - y)
        = (chi i x - chi i y) • (S i x - x) + chi i y • ((S i x - x) - (S i y - y)) := by
      module
    -- `chi i` is 1-Lipschitz, read off as a norm bound on the difference.
    have hc : ‖chi i x - chi i y‖ ≤ ‖x - y‖ := by
      have h := (hchi i).dist_le_mul x y
      rw [dist_eq_norm, dist_eq_norm] at h
      simpa using h
    -- `S i` is `K`-Lipschitz, likewise.  This is the only line that differs
    -- from the constant-`1` version.
    have hSK : ‖S i x - S i y‖ ≤ K * ‖x - y‖ := by
      have h := (hS i).dist_le_mul x y
      rw [dist_eq_norm, dist_eq_norm] at h
      have hK0 : 0 ≤ K := le_trans (by norm_num) hK
      have h' : ‖S i x - S i y‖ ≤ (Real.toNNReal K : ℝ) * ‖x - y‖ := by simpa using h
      rwa [Real.toNNReal_of_nonneg hK0] at h'
    -- The displacement difference `d x - d y = (S i x - S i y) - (x - y)`
    -- has norm at most `(K + 1) * ‖x - y‖`.
    have hdd : ‖(S i x - x) - (S i y - y)‖ ≤ (K + 1) * ‖x - y‖ := by
      have heq : (S i x - x) - (S i y - y) = (S i x - S i y) - (x - y) := by abel
      rw [heq]
      calc ‖(S i x - S i y) - (x - y)‖ ≤ ‖S i x - S i y‖ + ‖x - y‖ := norm_sub_le _ _
        _ ≤ K * ‖x - y‖ + ‖x - y‖ := add_le_add hSK (le_refl _)
        _ = (K + 1) * ‖x - y‖ := by ring
    -- Triangle inequality first, then one `norm_smul` per term: this avoids
    -- letting a single `ring` collapse the expression out of reach.
    rw [hid]
    have e1 : ‖(chi i x - chi i y) • (S i x - x)‖ ≤ ‖x - y‖ * M := by
      rw [norm_smul]
      exact mul_le_mul hc (hSiy i x) (norm_nonneg _) (norm_nonneg _)
    have e2 : ‖chi i y • ((S i x - x) - (S i y - y))‖ ≤ L * ((K + 1) * ‖x - y‖) := by
      rw [norm_smul]
      have h2 := mul_le_mul (hchiL i y) hdd (norm_nonneg _) hL
      exact h2
    calc ‖(chi i x - chi i y) • (S i x - x) + chi i y • ((S i x - x) - (S i y - y))‖
        ≤ ‖(chi i x - chi i y) • (S i x - x)‖
            + ‖chi i y • ((S i x - x) - (S i y - y))‖ := norm_add_le _ _
      _ ≤ ‖x - y‖ * M + L * ((K + 1) * ‖x - y‖) := add_le_add e1 e2
      _ = (M + (K + 1) * L) * ‖x - y‖ := by ring
  -- Sum the per-index estimates and absorb the constant through the sum.
  calc ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖
      = ‖∑ i, (chi i x • (S i x - x) - chi i y • (S i y - y))‖ := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖chi i x • (S i x - x) - chi i y • (S i y - y)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (M + (K + 1) * L) * ‖x - y‖ := Finset.sum_le_sum fun i _ => hper i
    _ = (∑ i : Fin n, (M + (K + 1) * L)) * ‖x - y‖ := (Finset.sum_mul _ _ _).symm
