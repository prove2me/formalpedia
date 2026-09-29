-- Prove2me | Theorems.Thm_Hadwiger_not_colorable_cone
-- name    : Hadwiger.not_colorable_cone
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:42:59.9072+00:00
-- url     : https://prove2.me/theorems/36db01b1-8249-40f6-8df8-cc46f88b44cc
-- title:
--   The cone needs one more colour than `G`.
-- statement:
--   **The cone needs one more colour than `G`.**
--
--   ```lean
--   theorem Hadwiger.not_colorable_cone{k : ℕ} (h : ¬ G.Colorable k) : ¬ (cone G).Colorable (k + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerMonotone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerMonotone.lean#L97

-- Thm stub generated from Probability/HadwigerMonotone.lean
import Mathlib
import Definitions.Def_Probability_HadwigerMonotone
import Definitions.Def_Probability_HadwigerSmallCases
/-
  Hadwiger's Conjecture is Monotone in `k`
  ========================================

  A structural theorem about the conjecture itself rather than about a single
  graph: **if Hadwiger's conjecture holds for the parameter `k+1`, it holds for
  `k`**.  The proof is the classical *apex* (cone) construction: adjoin to `G` a
  new vertex joined to everything.  The cone needs one colour more than `G`, so
  the assumed case produces a `K_{k+2}` model in the cone; deleting the (unique)
  branch set that contains the apex leaves a `K_{k+1}` model inside `G`.

  Main results:

  * `Hadwiger.cone`                      : the apex construction.
  * `Hadwiger.not_colorable_cone`        : `¬ G.Colorable k → ¬ (cone G).Colorable (k+1)`.
  * `Hadwiger.completeMinor_of_cone`     : a `K_{n+1}` minor of `cone G` yields a
                                           `Kₙ` minor of `G`.
  * `Hadwiger.hadwiger_monotone`         : `HadwigerProperty (k+1) → HadwigerProperty k`.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the conjecture should get *harder* as `k` grows, so
    the family `HadwigerProperty k` should be decreasing.  The apex construction
    is the standard tool.
  Experiment (Experimenter): two independent halves.  (i) Colouring: from a
    `(k+1)`-colouring of the cone, the apex colour `a` is missed by every other
    vertex, and the "delete colour `a`" map `Fin (k+1) → Fin k` is injective off
    `a`, producing a `k`-colouring of `G`.  (ii) Minors: the apex lies in at most
    one branch set (disjointness), so `Fin.succAbove` selects `k+1` branch sets
    avoiding it; each is contained in the copy of `V`, and walks inside them
    never see the apex, so they pull back to `G` along `Sum.inl`.
  Analysis (Analyst): the walk pull-back is the only genuinely inductive step; it
    needs that the branch set contains no apex, which is exactly the reason for
    discarding one branch set rather than intersecting.
  Critique (Critic): the case `k = 0` must be treated separately, since there is
    no injection `Fin 1 ∖ {a} → Fin 0`; there the cone contains an edge and so is
    not `1`-colourable directly.
  Synthesis (PI): `HadwigerProperty` is antitone, so the conjecture for a single
    large `k` subsumes all smaller ones — and the unresolved cases `k ≥ 5` are
    genuinely the hardest.
  -- !-- Lab Notes -- !--
-/

set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### The apex construction -/





/-! ### The cone needs one more colour -/

theorem Hadwiger.not_colorable_cone{k : ℕ} (h : ¬ G.Colorable k) : ¬ (cone G).Colorable (k + 1) := by sorry
