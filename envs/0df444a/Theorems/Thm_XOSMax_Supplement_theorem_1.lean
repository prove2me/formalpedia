-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_1
-- name    : XOSMax.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:34:16.026682+00:00
-- url     : https://prove2.me/theorems/848a45dc-0d7d-5178-aa0d-2f276e3a5780
-- title:
--   Theorem 1 — deterministic $\max(1,\varepsilon n)$-approximation in $O(n^{\lceil1/\varepsilon\rceil})$ time
-- statement:
--   For every $\varepsilon>0$ there is a constant $C$ such that, on every nonempty finite ground set, one deterministic value-oracle program chosen before the input function returns a $\max(1,\varepsilon n)$-maximizer of every XOS function and has charged cost at most
--   $$
--   Cn^{\lceil1/\varepsilon\rceil}.
--   $$
--   The program includes the singleton preprocessing of Section 2, so no positivity assumption remains in the theorem.
--
--   Differences from the source:
--   - encoding: an $(\varepsilon n)$-approximation for every $\varepsilon>0$ → a $\max(1,\varepsilon n)$-approximation; reason: ratios are defined only for $\alpha\ge1$, and the algorithm is exact when $\varepsilon n<1$
--   - encoding: deterministic value-oracle algorithm running in $O(n^{\lceil1/\varepsilon\rceil})$ time → an oracle program fixed before $f$, with one constant depending only on $\varepsilon$ and a bound on oracle calls plus charged elementary steps; reason: this is the paper's value-oracle program and constant-time generation model
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 1, p.2; Algorithm 1 and proof, pp.3-4

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_OracleProg

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Theorem 1.** For every `ε > 0`, one deterministic value-oracle algorithm returns a
`max(1, εn)`-maximizer of every XOS function using `O(n^⌈1/ε⌉)` charged operations
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Theorem 1, p.2).

**Formalization Note** The program is chosen from `ε` and the enumeration `L` before the input
function or any width. It includes the §2 singleton preprocessing, so the theorem has no sign
hypothesis. The constant depends on `ε` only and is chosen before the ground type. The ratio is
clamped at `1` because the source defines approximation ratios only for `α ≥ 1`; in the clamped
case Algorithm 1 is exhaustive and exact. -/
theorem theorem_1 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
        L.Nodup → L.toFinset = Finset.univ →
        ∃ A : OracleProg E (Finset E), ∀ f : Finset E → ℝ,
          (∃ k : ℕ, IsKXOS k f) →
          IsMaximizerApprox Finset.univ (max 1 (ε * Fintype.card E)) f (run f A).1 ∧
          (run f A).2 ≤ C * Fintype.card E ^ Nat.ceil (1 / ε) := by sorry

end XOSMax.Supplement
