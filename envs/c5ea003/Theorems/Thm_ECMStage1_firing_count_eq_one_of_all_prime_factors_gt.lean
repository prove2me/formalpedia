-- Prove2me | Theorems.Thm_ECMStage1_firing_count_eq_one_of_all_prime_factors_gt
-- name    : ECMStage1.firing_count_eq_one_of_all_prime_factors_gt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:32:15.160986+00:00
-- url     : https://prove2.me/theorems/75db21e9-994e-4fe3-913f-c3c3c15018e7
-- title:
--   The `found_q` control.
-- statement:
--   **The `found_q` control.**  If every prime factor of the order exceeds the
--   smoothness bound, only the identity fires: the order-completion rate is exactly
--   `1/m`, so success at such a factor cannot be order completion.
--
--   ```lean
--   theorem ECMStage1.firing_count_eq_one_of_all_prime_factors_gt{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0)
--       (hlarge : ∀ q ∈ m.primeFactors, B < q) : Nat.gcd m (stage1Scalar B) = 1 := by sorry
--
--   /-! ## Rank-two groups: the actual shape of `E(𝔽_p)` -/
--
--
--
--   /-! ## Against the collision baseline -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ECMStage1SmoothPart.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ECMStage1SmoothPart.lean#L54

-- Thm stub generated from Shared/ECMStage1SmoothPart.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1OrderCompletion

/-!
# The smooth part is the whole story: structure of the stage-1 firing count

Two files up we showed that stage-1 firing is the divisibility `orderOf g ∣ k(B)`, and
that the number of firing points of a cyclic group of order `m` is exactly `gcd(m, k(B))`.
This file identifies that number structurally and pushes the picture to the group shape
that actually occurs for elliptic curves over a prime field (a product of at most two
cyclic groups), and to the analytic comparison with the collision heuristic.

* `gcd_stage1Scalar_isGreatest`: `gcd(m, k(B))` **is** the largest `B`-powersmooth
  divisor of `m`, in the divisibility order.  So "how often does stage 1 fire" is
  literally "how big is the powersmooth part of the order".
* `firing_count_eq_one_of_all_prime_factors_gt`: if every prime factor of the order
  exceeds the bound, the firing count collapses to `1` (only the identity).  This is
  the `found_q` control in exact form: at the large prime factor of the modulus,
  order completion contributes a rate of `1/m`, so any hits there measure something
  else entirely.
* `card_firingSet_prod`: for a rank-two group `ℤ/m₁ × ℤ/m₂` — the actual shape of
  `E(𝔽_p)` — the firing count is the product `gcd(m₁,k)·gcd(m₂,k)` of the two
  smooth parts, and it is at least as large as in the cyclic case
  (`rank_two_fires_at_least_as_often`).
* `orderCompletion_exceeds_collision_baseline`: the analytic comparison.  Since
  `1 - exp(-x) ≤ x`, an order-completion rate above `1.44·B/m` provably exceeds the
  folklore collision baseline `1 - exp(-1.44·B/m)`; the numeric witness of the
  previous file is the special case `m = 720, B = 10`.
-/

open ECMStage1

open Finset

/-! ## The firing count is the powersmooth part of the order -/

theorem ECMStage1.firing_count_eq_one_of_all_prime_factors_gt{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0)
    (hlarge : ∀ q ∈ m.primeFactors, B < q) : Nat.gcd m (stage1Scalar B) = 1 := by sorry
