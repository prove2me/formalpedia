-- Prove2me | Theorems.Thm_A166944Research_a166944_horizon_cap_from_45895573
-- name    : A166944Research.a166944_horizon_cap_from_45895573
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-18T07:04:35.260201+00:00
-- url     : https://prove2.me/theorems/ee916f85-a916-4387-ae3c-5861f10a8f8d
-- title:
--   The A166944 canonical replay keeps its terminal horizon below 3M+4
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944, $d_n = a_n - a_{n-1}$ its first differences and $D_n = a_n - n$ its offset from the identity. Let $M$ be a difference record whose value is known to be the greater member of a twin-prime pair, so that $d_{M+2} = M$; the **canonical replay** starts at the state $(M+2,\;2M-2)$ and jumps from each state to the next index at which the recursion's `gcd` is nontrivial. Write $(sf,Cf)$ for the state at which it terminates.
--
--   This theorem bounds the terminal horizon:
--
--   $$Cf \;\le\; 3M + 4 .$$
--
--   It is one half of a pair of caps that together replace the older, stronger **travel bound** $2(sf-(M+2)) \le M$ in the induction deriving the index theorem and the twin-primality of records. The companion cap,
--
--   $$4\,sf \;\le\; 7M - 1 ,$$
--
--   is strictly weaker than the travel bound -- travel gives $4\,sf \le 6M+8$, so the relaxation is $M/4$, about $11.5$ million at the threshold $45895573$. The pair does not imply the travel bound: at $M = 45895573$ the pair $(sf, Cf) = (80317252,\,137686723)$ satisfies both caps and violates travel, so the decomposition is a genuine weakening rather than a restatement.
--
--   ## Role
--
--   This is the cap that the replay's **crossing** branch consumes, and that branch is the reason the decomposition is worth having: it reaches its conclusion through an existing theorem about horizon growth and does not depend on the relaxed index cap at all. So the case analysis splits the obstruction, and only the quiet branch consumes the harder half.
--
--   ## Where it stands
--
--   The statement is not proved here. It is a uniform statement about the terminal state of a canonical replay, and the development's finite certificates -- kernel-verified through record $11{,}751{,}795{,}061$ -- cover only finitely many records. What has changed with this pair of caps is the strength of the target, not whether the target is reached.
--
--   **Formalization Note** The lower bound $45895573$ is where the development's explicit replay certificates stop; below it the statement is discharged by replay. `IsGreaterTwinPrime M` is carried because the route is an induction that only needs the caps after a record already known to be a twin prime, which is how the development avoids circularity.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). Machine-checked at https://github.com/tara-sooo/A166944-Lean: A166944/TwoCapGate.lean, A166944/TwoCapTarget.lean.

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research

theorem a166944_horizon_cap_from_45895573 :
    ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4 := by
  sorry

end A166944Research
