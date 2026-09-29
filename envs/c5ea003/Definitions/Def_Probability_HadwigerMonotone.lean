-- Prove2me | Definitions.Def_Probability_HadwigerMonotone
-- name    : Probability_HadwigerMonotone
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:47.37118+00:00
-- url     : https://prove2.me/theorems/9246f516-868c-4980-8a6e-ff3fbfd697ac
-- title:
--   Aether Catalog definitions — Probability_HadwigerMonotone
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerMonotone`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerMonotone.lean by skeleton subtraction
import Mathlib
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
namespace Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### The apex construction -/

/-- `cone G` adjoins to `G` a new (apex) vertex adjacent to every old vertex. -/
def cone (G : SimpleGraph V) : SimpleGraph (V ⊕ Unit) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (a | a) (b | b) h <;> simp_all
    exact h.symm
  loopless := ⟨by
    rintro (a | a) h
    · exact G.irrefl h
    · exact h⟩




/-! ### The cone needs one more colour -/

/-- Deleting the colour `a` from `Fin (k+1)`. -/
private def dropColor (k : ℕ) (a : Fin (k + 1)) (hk : 0 < k) (c : Fin (k + 1)) : Fin k :=
  if h : c.val < a.val then ⟨c.val, by omega⟩ else ⟨c.val - 1, by omega⟩



/-! ### Pulling a minor of the cone back to `G` -/





end Hadwiger


