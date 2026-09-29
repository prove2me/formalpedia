-- Prove2me | solution 1 for GenericRecovery.card_sq_fiber_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:38:07.679541+00:00
-- url     : https://prove2.me/submissions/0fc2924d-8cfc-4bc0-b4a9-28f4ff7b95a2

-- Sol generated from Combinatorics/GenericRecoveryHintTaxonomy.lean
import Mathlib
import Definitions.Def_Combinatorics_GenericRecoveryHintTaxonomy
import Theorems.Thm_GenericRecovery_sq_fiber_eq
import Theorems.Thm_GenericRecovery_two_pow_dvd_two_mul
import Theorems.Thm_GenericRecovery_zmod_eq_iff
/-
# GENERIC-RECOVERY: a closed taxonomy of `t`-bit hints

Formal companion to experiment 390 (`55_GenericRecovery_HintTaxonomy`), and a
sequel to `Combinatorics.DialThresholdNoAmplification` / `…Sharpness`.

**The question.**  A factoring-style adversary is handed a *hint*: a function
`h` of the secret `p`, whose value costs `t` bits to transmit.  How much can the
hint shrink the search for `p`?  The experiment measured, on exact `k`-bit prime
sets (`k = 14…25`), that a random GF(2) linear form of the bits of `p` splits
the candidate set into classes of size *exactly* `|P_k| / 2^t`; that
multiplicative and XOR-mask value hints only ever realise `2^{t-1}` values and
so lose a bit; and that the trace hint `s = p + q mod 2^t` is *sub-bit*, costing
a constant factor `C_t` extra because `p` is pinned only up to the roots of a
quadratic.  This file proves all four legs.

## Contents

* **§1 The master bound** — `GenericRecovery.card_le_card_image_mul_worstCost`
  and `GenericRecovery.worstCost_ge_of_card_image_le`: a hint with at most `2^t`
  values always leaves some class of size `≥ |S| / 2^t`.  *No hint of `t` bits
  ever cuts the search by more than `2^t`.*
* **§2 Generic linear hints are information-exact** —
  `GenericRecovery.card_fiber_addHom` (every fibre of a surjective group hint
  has the *same* size) and `GenericRecovery.card_fiber_gf2` (`= 2^{k-t}` on the
  bit cube).  This is the "no anomalous class, no super-resolution" leg.
* **§2b Position-freeness** — `GenericRecovery.card_fiber_coordRestrict`: reading
  the bits of `p` in *any* position set `A` leaves exactly `2^{k-|A|}`
  candidates.  Counting cannot see position; whatever Coppersmith gains from a
  *contiguous top half* is algorithmic, not information-theoretic.
* **§3 Value hints are parity-constrained** —
  `GenericRecovery.worstCost_mulHint_ge` and
  `GenericRecovery.worstCost_xorHint_ge`: `c·p mod 2^t` and `(p XOR m) mod 2^t`
  on odd `p` realise at most `2^{t-1}` values, so their classes are twice as big
  as a bit-vector hint's.  One bit of the `t` is spent on a constant.
* **§4 Data processing** — `GenericRecovery.worstCost_le_worstCost_comp`
  (post-processing never amplifies) and `GenericRecovery.worstCost_pair_ge`
  (bits of independent hints add, they do not multiply).
* **§5 Public hints are sealed** — `GenericRecovery.worstCost_of_public`: a hint
  recomputable from data the adversary already has (`N`) has a single class,
  i.e. zero information.
* **§6 The trace hint loses two bits** — `GenericRecovery.card_sq_fiber_eq_four`:
  for `t ≥ 3` the congruence `x² ≡ u² (mod 2^t)` has **exactly four** odd
  solutions, so the trace hint `s = p+q mod 2^t` (which determines `p` only
  through `(2p-s)² = s² - 4N`) pins `p mod 2^t` to `C_t = 4` classes.  That is
  the measured saturation `C_t ∈ {4, 8}` and the `log₂ C_t ≈ 2–3` bits lost.
* **§7 Synthesis** — `GenericRecovery.taxonomy`: the three regimes in one
  statement, `2^t` / `2^{t-1}` / `2^{t-2}` usable bits.
-/

open GenericRecovery

open Finset

/-! ## 1.  The recovery cost of a hint and the master bound -/

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]







/-! ## 2.  Generic (linear) hints are information-exact

A hint that is a group homomorphism has *all* fibres of the same size: there is
no anomalous class, hence no reading of the hint that resolves `p` better than
average.  This is the exact statement that the experiment measured as
`|P_k| / 2^t` with no outliers. -/


variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [DecidableEq H]





variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]








/-! ## 3.  Value hints are parity-constrained: one bit is always wasted -/






/-! ## 4.  Data processing: hints never gain information downstream -/



/-! ## 5.  Public hints are sealed: an `N`-checkable hint has zero information -/


/-! ## 6.  The trace hint is sub-bit: exactly four square roots mod `2^t`

The trace hint gives `s ≡ p + q (mod 2^t)` with `N = p·q` public.  Completing
the square turns this into `(2p - s)² = s² - 4N`, so the adversary learns a
*square* mod a power of two, and `p` is pinned only up to the square roots.  We
prove there are exactly four of them for `t ≥ 3`: `log₂ C_t = 2` bits are burnt
by the root ambiguity, exactly the constant-factor blow-up measured. -/








theorem not_dvd_of_odd (m : ℕ) {u : ℤ} (hu : Odd u) (hm : 1 ≤ m) : ¬ (2:ℤ) ^ m ∣ u := by
  intro h
  have h2 : (2:ℤ) ∣ u := dvd_trans (dvd_pow_self 2 (by omega)) h
  obtain ⟨k, hk⟩ := hu; obtain ⟨j, hj⟩ := h2; omega


/-! ## 7.  Synthesis: the taxonomy in one statement -/



open GenericRecovery in
theorem solution(n : ℕ) (u : ℤ) (hu : Odd u) :
    #{x ∈ (univ : Finset (ZMod (2 ^ (n + 3)))) |
        x ^ 2 = ((u : ℤ) : ZMod (2 ^ (n + 3))) ^ 2} = 4 := by
  rw [sq_fiber_eq n u hu]
  have key : ∀ v w : ℤ, ¬ ((2:ℤ) ^ (n + 3) ∣ v - w) →
      ((v : ℤ) : ZMod (2 ^ (n + 3))) ≠ ((w : ℤ) : ZMod (2 ^ (n + 3))) := by
    intro v w hvw hEq
    exact hvw ((zmod_eq_iff n v w).mp hEq)
  -- the three genuinely different differences
  have d1 : ¬ (2:ℤ) ^ (n + 3) ∣ 2 * u := by
    intro h
    exact not_dvd_of_odd (n + 2) hu (by omega) (two_pow_dvd_two_mul h)
  have d2 : ¬ (2:ℤ) ^ (n + 3) ∣ (2:ℤ) ^ (n + 2) := by
    intro h
    have hle := Int.le_of_dvd (by positivity) h
    have : (2:ℤ) ^ (n + 2) < 2 ^ (n + 3) := by
      apply pow_lt_pow_right₀ (by norm_num)
      omega
    omega
  have d3 : ∀ ε : ℤ, ε = 1 ∨ ε = -1 → ¬ (2:ℤ) ^ (n + 3) ∣ (2 * u + ε * 2 ^ (n + 2)) := by
    intro ε hε h
    have h' : (2:ℤ) ^ (n + 2) ∣ u + ε * 2 ^ (n + 1) := by
      refine two_pow_dvd_two_mul ?_
      have hrw : 2 * (u + ε * 2 ^ (n + 1)) = 2 * u + ε * 2 ^ (n + 2) := by ring
      rw [hrw]; exact h
    have h2 : (2:ℤ) ∣ u + ε * 2 ^ (n + 1) := dvd_trans (dvd_pow_self 2 (by omega)) h'
    have h3 : (2:ℤ) ∣ ε * 2 ^ (n + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) ε
    obtain ⟨k, hk⟩ := hu
    obtain ⟨j, hj⟩ := h2
    obtain ⟨i, hi⟩ := h3
    omega
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact key _ _ (by rw [show u + 2 ^ (n + 2) - (-u + 2 ^ (n + 2)) = 2 * u by ring]; exact d1)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨key _ _ ?_, key _ _ ?_⟩
    · rw [show -u - (u + 2 ^ (n + 2)) = -(2 * u + 1 * 2 ^ (n + 2)) by ring]
      exact fun h => d3 1 (Or.inl rfl) ((dvd_neg).mp h)
    · rw [show -u - (-u + 2 ^ (n + 2)) = -(2 ^ (n + 2)) by ring]
      exact fun h => d2 ((dvd_neg).mp h)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_⟩
    · rw [show u - -u = 2 * u by ring]; exact d1
    · rw [show u - (u + 2 ^ (n + 2)) = -(2 ^ (n + 2)) by ring]
      exact fun h => d2 ((dvd_neg).mp h)
    · rw [show u - (-u + 2 ^ (n + 2)) = 2 * u + (-1) * 2 ^ (n + 2) by ring]
      exact d3 (-1) (Or.inr rfl)
