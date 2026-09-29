-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellQ_dvd_index_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:03:09.484622+00:00
-- url     : https://prove2.me/submissions/e74a3d5a-b47c-4b79-904a-2f33eb59b5f0

-- Sol generated from Novelty/PellSpineCompanionDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_gcd
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_pos
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_strictMono
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_dvd_pellP_two_mul
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_succ_eq_add
/-
# The companion divisibility law on the Pell spine

`Novelty.PellSpineDivisibility` shows that the Pell numbers `P` form a strong divisibility
sequence while the half-companion sequence `Q` does **not** (`gcd (Q 3) (Q 6) = 1`).  That
refutation leaves the real question open: *exactly when* does `Q m` divide `Q n`?

This file answers it completely.  For every `m ≥ 2`,

`Q m ∣ Q n  ↔  n = m * k for some odd k`,

a parity-graded divisibility law with no analogue among the `P`'s.  The proof runs in two
independent halves:

* **index step** — `Q m ∣ P (2m)` and `Q n ∣ P (2n)` push the hypothesis into the strong
  divisibility law for `P`, forcing `Q m ∣ P (2 gcd(m,n))`; if `gcd(m,n) < m` the divisor
  exceeds the dividend, so `m ∣ n`;
* **parity step** — modulo `Q m` the companion sequence satisfies the two-step recursion
  `Q (a + 2m) ≡ 2 P m ^ 2 * Q a`, so `Q (2jm) ≡ (2 P m ^ 2) ^ j`, a unit mod `Q m`
  because `Q m` is odd and coprime to `P m`.  Even multiples are therefore ruled out.

## Proved

* `pellQ_odd`, `pellQ_coprime_two_pellP_sq` — the arithmetic units used by the parity step;
* `pellQ_add_two_mul_modEq` — `Q (a + 2m) ≡ 2 P m ^ 2 * Q a [MOD Q m]`;
* `pellQ_even_multiple_modEq` — `Q (2jm) ≡ (2 P m ^ 2) ^ j [MOD Q m]`;
* `pellQ_coprime_even_multiple` — `gcd (Q m) (Q (2jm)) = 1`;
* `pellQ_dvd_index_dvd` — `Q m ∣ Q n → m ∣ n` for `m ≥ 2`;
* `pellQ_dvd_iff` — **the companion divisibility law**;
* `pellQ_gcd_dvd`, `pellQ_gcd_eq_one_of_even_quotient`, `pellQ_gcd_law` — **the companion
  gcd law**: `gcd (Q m) (Q n) = Q (gcd m n)` when both index quotients are odd, and `1`
  otherwise, with no side condition on `m` and `n`;
* `pellQ_gcd_of_odd_quotients` — the graded gcd statement that survives the refutation;
* summation identities `pellQ_sum`, `pellP_sum`, `pellP_sq_sum` tying the two strands
  of the spine together.

## Refuted

* `not_pellQ_dvd_all_multiples` — `Q n ∣ Q (kn)` fails for even `k`: `Q 2 = 3 ∤ 17 = Q 4`;
* `not_pellQ_dvd_iff_index_dvd` — divisibility of indices is **not** sufficient, by the
  same pair, so the parity grading in `pellQ_dvd_iff` cannot be dropped.
-/

open Catalog.Novelty.PellSpine

open Finset

/-! ## Arithmetic units modulo `Q m` -/



/-! ## The parity step -/




/-! ## The index step -/

/-- For `m ≥ 2` the companion value strictly dominates the Pell value. -/
theorem pellP_lt_pellQ {m : ℕ} (hm : 2 ≤ m) : pellP m < pellQ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have h := pellQ_succ_eq_add k
  have : 0 < pellP k := pellP_pos hk
  omega



/-! ## The companion divisibility law -/







/-! ## Refutations -/





/-! ## Summation identities linking the two strands -/





open Catalog.Novelty.PellSpine in
theorem solution{m n : ℕ} (hm : 2 ≤ m) (h : pellQ m ∣ pellQ n) : m ∣ n := by
  set g := Nat.gcd m n with hg
  have hdvd2m : pellQ m ∣ pellP (2 * m) := pellQ_dvd_pellP_two_mul m
  have hdvd2n : pellQ m ∣ pellP (2 * n) := h.trans (pellQ_dvd_pellP_two_mul n)
  have hgcd : pellQ m ∣ pellP (2 * g) := by
    have : pellQ m ∣ Nat.gcd (pellP (2 * m)) (pellP (2 * n)) := Nat.dvd_gcd hdvd2m hdvd2n
    rwa [pellP_gcd, show Nat.gcd (2 * m) (2 * n) = 2 * g by rw [hg, Nat.gcd_mul_left]] at this
  have hgm : g ∣ m := Nat.gcd_dvd_left m n
  rcases Nat.lt_or_ge g m with hlt | hge
  · exfalso
    have h2g : 2 * g ≤ m := by
      obtain ⟨c, hc⟩ := hgm
      have hg0 : 0 < g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · exfalso
          have : m = 0 := Nat.eq_zero_of_gcd_eq_zero_left (hg ▸ h0)
          omega
        · exact h0
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with hc1 | hc2
        · interval_cases c <;> omega
        · exact hc2
      calc 2 * g ≤ c * g := Nat.mul_le_mul_right g hc2
        _ = m := by rw [hc, Nat.mul_comm]
    have hpos : 0 < pellP (2 * g) := by
      have hg0 : 0 < g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · exfalso
          have : m = 0 := Nat.eq_zero_of_gcd_eq_zero_left (hg ▸ h0)
          omega
        · exact h0
      exact pellP_pos (by omega)
    have hle : pellP (2 * g) ≤ pellP m := pellP_strictMono.monotone h2g
    have hlt' : pellP m < pellQ m := pellP_lt_pellQ hm
    have := Nat.le_of_dvd hpos hgcd
    omega
  · have : g = m := le_antisymm (Nat.le_of_dvd (by omega) hgm) hge
    exact this ▸ Nat.gcd_dvd_right m n
