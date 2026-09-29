-- Prove2me | solution 1 for RLHF.kl_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:08:41.446982+00:00
-- url     : https://prove2.me/submissions/d7399cce-2ee5-41d5-99b6-b33f54a9576c

-- Thm stub generated from NumberTheory/RLHFGibbsVariational.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational

/-!
# The Gibbs variational principle for KL-regularized RLHF

This module is the root of the RLHF thread of the catalog.  It sets up the finite
KL-regularized alignment problem and proves the Gibbs variational principle that all the
downstream files use.

For a finite response space `Ω`, a reward model `r : Ω → ℝ`, a strictly positive reference
(SFT) policy `p : Ω → ℝ` and a KL coefficient `β > 0`, the RLHF objective at a policy `q` is

```
objective β r p q = 𝔼_q[r] − β · KL(q ‖ p).
```

Main results.

* `RLHF.kl_nonneg` — Gibbs' inequality: `KL(q ‖ p) ≥ 0` for a distribution `q` and a
  positive distribution `p`.
* `RLHF.kl_eq_zero_iff` — the equality case: `KL(q ‖ p) = 0 ↔ q = p`.
* `RLHF.objective_eq_sub_kl_gibbs` — the *pivot identity*
  `objective β r p q = β log Z(β) − β · KL(q ‖ π_β)`, where `π_β` is the Gibbs (tilted)
  policy and `Z(β) = ∑_y p y · exp(r y / β)` the partition function.
* `RLHF.variational_principle` and `RLHF.variational_strict` — consequently `β log Z` is the
  optimal value of the RLHF objective, attained *only* at the Gibbs policy
  (`RLHF.objective_gibbs`).
* `RLHF.reference_le_free_energy` — RLHF never hurts: the optimal value dominates the value
  of the reference policy.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Policies -/




/-! ## 2. Kullback–Leibler divergence -/

/- The proof and helper below are ported from Paul Klemstine, Aether Catalog,
   NumberTheory/RLHFGibbsVariational.lean, commit 53c2925a02, lines52–118.
   Only helper/solution names are changed; no Nonempty hypothesis is added. -/

private theorem local_kl_term_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * Real.log (a / b) := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simp
    linarith
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (b / a) = -Real.log (a / b) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    have h3 : a * (1 - b / a) = a - b := by field_simp
    have h4 : a * (1 - b / a) ≤ a * Real.log (a / b) := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      linarith
    linarith

theorem solution {q p : Ω → ℝ} (hq : IsDist q) (hp : IsPosDist p) :
    klDiv q p = 0 ↔ q = p := by
  constructor
  · intro h0
    have hterm : ∀ y ∈ (univ : Finset Ω), q y - p y ≤ q y * Real.log (q y / p y) :=
      fun y _ => local_kl_term_le (hq.1 y) (hp.1 y)
    have hsum : ∑ y, (q y - p y) = ∑ y, q y * Real.log (q y / p y) := by
      rw [Finset.sum_sub_distrib, hq.2, hp.2]
      simpa [klDiv] using h0.symm
    have heq := (Finset.sum_eq_sum_iff_of_le hterm).1 hsum
    funext y
    have hy := heq y (Finset.mem_univ y)
    rcases eq_or_lt_of_le (hq.1 y) with hq0 | hqpos
    · exfalso
      rw [← hq0] at hy
      simp at hy
      linarith [hp.1 y]
    · by_contra hne
      have hratio : p y / q y ≠ 1 := by
        intro h
        exact hne (by field_simp at h; linarith)
      have hlt : Real.log (p y / q y) < p y / q y - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos (hp.1 y) hqpos) hratio
      have h2 : Real.log (p y / q y) = -Real.log (q y / p y) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      have h3 : q y * (1 - p y / q y) < q y * Real.log (q y / p y) := by
        have : 1 - p y / q y < Real.log (q y / p y) := by linarith
        exact mul_lt_mul_of_pos_left this hqpos
      have h4 : q y * (1 - p y / q y) = q y - p y := by field_simp
      linarith
  · rintro rfl
    have : ∀ y, q y * Real.log (q y / q y) = 0 := by
      intro y
      rw [div_self (ne_of_gt (hp.1 y))]
      simp
    simp [klDiv]
