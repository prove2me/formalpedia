-- Prove2me | Theorems.Thm_RLHF_gibbs_exponent_zero_marginal
-- name    : RLHF.gibbs_exponent_zero_marginal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:48:42.770485+00:00
-- url     : https://prove2.me/theorems/c96fbc41-99e2-476d-bcff-fe426e000326
-- title:
--   The exponent-zero (i.e.
-- statement:
--   The exponent-zero (i.e. `p ∤ n`) marginal probability of the aligned policy.
--
--   ```lean
--   theorem RLHF.gibbs_exponent_zero_marginal{β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p)
--       (hq : 0 < q) :
--       ∑ b : Fin (B + 1),
--           gibbsPolicy β (zetaReward (A := A) (B := B) β s p q) (uniformDist (Smooth A B))
--             (⟨0, Nat.succ_pos A⟩, b)
--         = 1 / localZeta s p A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFZetaDivisibility.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFZetaDivisibility.lean#L24

-- Thm stub generated from NumberTheory/RLHFZetaDivisibility.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy

/-!
# Divisibility statistics of the aligned (zeta) policy

For the Dirichlet reward on the `{p,q}`-smooth response space, the optimal RLHF policy is
the truncated zeta distribution (`RLHF.gibbs_zeta_policy`).  Here we compute the
*arithmetic* statistics of the responses it emits.

* `RLHF.gibbs_exponent_zero_marginal` — the probability that the sampled response is
  **not divisible** by `p` equals `1 / localZeta s p A`.
* `RLHF.prob_dvd_lt_zetaWeight` — hence the probability that `p` divides the sampled
  response is strictly below `p^{-s}`, the classical Dirichlet density.
* `RLHF.tendsto_localZeta_euler_factor`, `RLHF.tendsto_prob_not_dvd` — as the exponent
  cutoff is lifted, these statistics converge exactly to the Golomb–Dirichlet values
  `1 - p^{-s}`: alignment reproduces the density of `p`-indivisible integers.
-/

open RLHF

open Finset Filter Topology

variable {A B : ℕ}

theorem RLHF.gibbs_exponent_zero_marginal{β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p)
    (hq : 0 < q) :
    ∑ b : Fin (B + 1),
        gibbsPolicy β (zetaReward (A := A) (B := B) β s p q) (uniformDist (Smooth A B))
          (⟨0, Nat.succ_pos A⟩, b)
      = 1 / localZeta s p A := by sorry
