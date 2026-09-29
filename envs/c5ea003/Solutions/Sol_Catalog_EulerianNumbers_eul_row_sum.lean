-- Prove2me | solution 1 for Catalog.EulerianNumbers.eul_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T04:38:47.011622+00:00
-- url     : https://prove2.me/submissions/2c039208-7051-4188-bf24-1aad2c967db8

/-
# `Catalog.EulerianNumbers.eul_row_sum`
Target `d0b84fd3` (Open, not deprecated at draft time; re-read live immediately before submitting).

NOT YET COMPILED — drafted while the build lock was held by another ship.

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`eul` is the Eulerian triangle (rows 1 / 1,1 / 1,4,1 / 1,11,11,1 / 1,26,66,26,1), and row `n`
sums to `n !`. Verified exactly for n = 1..15 by transcribing the definition clause-for-clause,
including ℕ truncated subtraction. It FAILS at n = 0, where the sum is empty but `0! = 1`, which
is exactly what `hn : 1 ≤ n` buys. Truncated subtraction never clamps in the range used.

THE STEP, derived before drafting. Split off the bottom term and shift with `sum_range_succ'`:

    S(n+1) = eul (n+1) 0 + ∑_{k<n} [ (k+2)·eul n (k+1) + (n-k)·eul n k ]

Reindexing the first sum costs exactly `eul n 0 = 1`, and its top term `(n+1)·eul n n` vanishes,
so the two constants cancel and `(k+1) + (n-k) = n+1` factors out:

    S(n+1) = ∑_{k<n} ((k+1) + (n-k))·eul n k = (n+1)·S(n) = (n+1)·n! = (n+1)!

Everything is kept additive: ℕ subtraction is avoided entirely except inside `eul` itself.

PROBED, NOT GUESSED:
  * `Catalog.EulerianNumbers.eul : ℕ → ℕ → ℕ` — name and namespace confirmed.
  * the three defining equations below all hold by `rfl` (confirmed in a probe).
  * `Finset.sum_range_succ  : ∑ x ∈ range (n+1), f x = ∑ x ∈ range n, f x + f n`
  * `Finset.sum_range_succ' : ∑ k ∈ range (n+1), f k = ∑ k ∈ range n, f (k+1) + f 0`
  * `Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`
-/
import Mathlib
import Definitions.Def_Speculative_NumberTheory_EulerianNumbers

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset Catalog.EulerianNumbers

/-! ### The defining equations, each confirmed to hold by `rfl` -/

theorem eul_succ_zero (n : ℕ) : eul (n + 1) 0 = 1 := rfl

theorem eul_zero_succ (k : ℕ) : eul 0 (k + 1) = 0 := rfl

theorem eul_succ_succ (n k : ℕ) :
    eul (n + 1) (k + 1) = (k + 2) * eul n (k + 1) + (n - k) * eul n k := rfl

/-! ### Off the end of the row

Stated as `n ≤ k → eul (n+1) (k+1) = 0` rather than `1 ≤ n → n ≤ k → eul n k = 0`, because the
latter's induction hypothesis is vacuous at `m = 0` and forces a special case. -/

theorem eul_vanish : ∀ n k : ℕ, n ≤ k → eul (n + 1) (k + 1) = 0 := by
  intro n
  induction n with
  | zero =>
      intro k _
      rw [eul_succ_succ, eul_zero_succ, Nat.zero_sub]
      ring
  | succ m ih =>
      intro k hk
      rw [eul_succ_succ, ih k (by omega), show m + 1 - k = 0 by omega]
      ring

/-- The top entry of row `n+1` is off the end, hence zero. -/
theorem eul_diag (m : ℕ) : eul (m + 1) (m + 1) = 0 := eul_vanish m m (le_refl m)

/-! ### The row sum -/

/-- **The target, verbatim.** -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, eul n k = Nat.factorial n := by
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- base case n = 1: the row is the single entry `eul 1 0 = 1`
      subst hm
      simp [eul_succ_zero]
    · -- step: m ≥ 1, so the induction hypothesis applies
      have hrow : ∑ k ∈ Finset.range m, eul m k = Nat.factorial m := ih hm
      -- split off the bottom term and shift the index
      rw [Finset.sum_range_succ' (fun k => eul (m + 1) k) m, eul_succ_zero]
      -- expand the recurrence in the shifted sum
      have hexp : ∑ k ∈ Finset.range m, eul (m + 1) (k + 1)
          = ∑ k ∈ Finset.range m, ((k + 2) * eul m (k + 1) + (m - k) * eul m k) :=
        Finset.sum_congr rfl (fun k _ => eul_succ_succ m k)
      rw [hexp, Finset.sum_add_distrib]
      -- reindexing the first sum costs exactly `eul m 0 = 1`, and its top term vanishes
      -- m ≥ 1, so m is a successor: the bottom entry is 1 and the diagonal entry vanishes
      have hm0 : eul m 0 = 1 := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        exact eul_succ_zero j
      have hmm : eul m m = 0 := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        exact eul_diag j
      have hshift : (∑ k ∈ Finset.range m, (k + 2) * eul m (k + 1)) + 1
          = ∑ k ∈ Finset.range m, (k + 1) * eul m k := by
        -- stated in the literal form `sum_range_succ'` produces, so no normalisation is assumed
        have h1 : ∑ k ∈ Finset.range (m + 1), (k + 1) * eul m k
            = (∑ k ∈ Finset.range m, (k + 1 + 1) * eul m (k + 1)) + (0 + 1) * eul m 0 :=
          Finset.sum_range_succ' (fun k => (k + 1) * eul m k) m
        have h2 : ∑ k ∈ Finset.range (m + 1), (k + 1) * eul m k
            = ∑ k ∈ Finset.range m, (k + 1) * eul m k := by
          rw [Finset.sum_range_succ, hmm, Nat.mul_zero, Nat.add_zero]
        rw [← h2, h1, hm0]
      -- now (k+1) + (m-k) = m+1 for every k < m, so the factor comes out
      have hfold : ∑ k ∈ Finset.range m, ((k + 1) + (m - k)) * eul m k
          = ∑ k ∈ Finset.range m, (m + 1) * eul m k := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hlt : k < m := Finset.mem_range.mp hk
        rw [show (k + 1) + (m - k) = m + 1 by omega]
      calc (∑ k ∈ Finset.range m, (k + 2) * eul m (k + 1))
              + (∑ k ∈ Finset.range m, (m - k) * eul m k) + 1
          = ((∑ k ∈ Finset.range m, (k + 2) * eul m (k + 1)) + 1)
              + (∑ k ∈ Finset.range m, (m - k) * eul m k) := by ring
        _ = (∑ k ∈ Finset.range m, (k + 1) * eul m k)
              + (∑ k ∈ Finset.range m, (m - k) * eul m k) := by rw [hshift]
        _ = ∑ k ∈ Finset.range m, ((k + 1) + (m - k)) * eul m k := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = ∑ k ∈ Finset.range m, (m + 1) * eul m k := hfold
        _ = (m + 1) * ∑ k ∈ Finset.range m, eul m k := (Finset.mul_sum _ _ _).symm
        _ = (m + 1) * Nat.factorial m := by rw [hrow]
        _ = Nat.factorial (m + 1) := (Nat.factorial_succ m).symm
