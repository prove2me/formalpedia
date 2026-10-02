-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_state_baseline_budget_violation
-- name    : syracuse_cycle_eq_one_of_state_baseline_budget_violation
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T03:27:29.912226+00:00
-- url     : https://prove2.me/theorems/5a1a55e6-4fbf-4777-8e1f-99cd0de58887
-- title:
--   Global Syracuse cycle-budget exclusion from a supplied state baseline
-- statement:
--   Let $B,m,p\in\mathbb N$ with $m>0$ and $p>0$. Write $T(n)=\operatorname{oddpart}(3n+1)$, assume $T^p(m)=m$, and define
--
--   $$K=\sum_{i=0}^{p-1}v_2(3T^i(m)+1).$$
--
--   Assume explicitly that every positive point $y<B$ returning under $T^p$ is trivial: $y=1$. If
--
--   $$(3B+1)^p<2^K B^p,$$
--
--   then
--
--   $$m=1.$$
--
--   This is a reusable implication from a supplied certified state baseline, not certification of any arbitrary baseline $B$. The supplied return period need not be minimal and the starting state need not be a cycle minimum. No state upper bound or upper period cap is assumed. Applying it at $B=2310000$ requires the existing Proved finite cycle-state baseline; any larger baseline must be proved separately. This theorem is a restricted cycle exclusion, not a full tail or Collatz convergence result.
-- source:
--   Derived exact product-budget implication from the public minimum-cycle product bound https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322 and periodic-reaches-one https://prove2.me/theorems/a46524f0-afd4-4232-b74a-8a95d7ab31a5 . Reuses the minimum selection and full indexed-period valuation transport from accepted source submission8b4d8157-4087-4099-acd1-6886fd04c8c2 of https://prove2.me/theorems/a7d0c485-99df-4f66-b8fe-0c50634a1a34 with credit to that argument and its public community supports. At the concrete certified baseline2310000, this expresses a known product-envelope mechanism exactly, not a claim of global mathematical novelty. The baseline premise is explicit; no unverified larger threshold is imported.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_cycle_eq_one_of_state_baseline_budget_violation (B m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hbelow : ∀ y : ℕ, 0 < y → syracuseStep^[p] y = y → y < B → y = 1)
    (hviolation : (3 * B + 1) ^ p <
      (2 : ℕ) ^ (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2) * B ^ p) :
    m = 1 := by sorry
