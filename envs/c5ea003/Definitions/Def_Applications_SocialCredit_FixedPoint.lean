-- Prove2me | Definitions.Def_Applications_SocialCredit_FixedPoint
-- name    : Applications_SocialCredit_FixedPoint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:05.296444+00:00
-- url     : https://prove2.me/theorems/feebc8af-93cb-4bee-b24b-a951ba6f2458
-- title:
--   Aether Catalog definitions — Applications_SocialCredit_FixedPoint
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SocialCredit.FixedPoint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SocialCredit/FixedPoint.lean by skeleton subtraction
import Mathlib

/-!
# Social Credit Scores as Fixed-Point Attractors

We model a **social credit system** as a map assigning to each member of a
population a *score* living in a totally ordered set (here the real line `ℝ`,
the prototypical complete, totally ordered value space).  Two structural
phenomena are made precise.

* **Extremal members.** On a compact population a continuous scoring map always
  realises a highest- and a lowest-scoring member (`credit_attains_max`,
  `credit_attains_min`).  This is the topological reason a social credit system
  always has identifiable "best" and "worst" ranked individuals.

* **Attractors of the update dynamics.** Credit is not static: each round a
  member's score is revised by a *reward* `c` plus a *damped memory* `k · (old
  score)` of the previous value.  When the damping factor satisfies
  `0 ≤ k < 1` the update map is a contraction, and every starting score
  converges to a single equilibrium `c / (1 - k)`, independent of the initial
  condition (`creditIterate_tendsto`).  The equilibrium is the unique fixed
  point (`creditEquilibrium_unique`).

* **Order-theoretic attractors.** Even without any contraction or continuity
  assumption, a *monotone* credit map on the score interval `[0,1]` must have an
  equilibrium score (`monotone_credit_has_fixedPoint`): a Knaster–Tarski fixed
  point obtained as the supremum of the sub-fixed points.
-/

open Filter Topology

namespace SocialCredit

/-! ## Extremal members of a compact population -/

/-
A continuous credit map on a nonempty compact population attains a maximum:
there is a highest-scoring member.
-/

/-
A continuous credit map on a nonempty compact population attains a minimum:
there is a lowest-scoring member.
-/

/-! ## The affine credit-update dynamics -/

/-- One round of credit revision: a fixed reward `c` plus a damped memory
`k · x` of the previous score `x`. -/
def creditStep (c k x : ℝ) : ℝ := c + k * x

/-- The score after `n` rounds of revision, starting from an initial score `x₀`. -/
def creditIterate (c k x₀ : ℝ) (n : ℕ) : ℝ := (creditStep c k)^[n] x₀

/-- The equilibrium (long-run) credit score `c / (1 - k)`. -/
noncomputable def creditEquilibrium (c k : ℝ) : ℝ := c / (1 - k)

/-
The equilibrium score is a fixed point of the update map.
-/

/-
Closed form for the score after `n` rounds.
-/

/-
**Fixed-point attractor.**  With damping `0 ≤ k < 1`, every starting score
converges to the equilibrium, independently of the initial condition.
-/

/-
The equilibrium is the *unique* fixed point of the update map (for `k ≠ 1`).
-/

/-! ## Order-theoretic attractor: Knaster–Tarski on the score interval -/

/-
**Knaster–Tarski for credit scores.**  A monotone credit map that keeps
scores inside `[0,1]` always has an equilibrium score in `[0,1]`, with no
continuity or contraction hypothesis.
-/

end SocialCredit


