-- Prove2me | Definitions.Def_Thm_BookSixth_continuous_cutoff
-- name    : Thm_BookSixth_continuous_cutoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T17:53:10.119991+00:00
-- url     : https://prove2.me/theorems/faf7628a-1f49-4817-ba2b-dd2f26b3689b
-- title:
--   A continuous cutoff equal to one on a compact set and zero off an open set
-- statement:
--   Let $K$ be a compact subset of $\mathbb R^3$ and let $O$ be an open set with $K \subseteq O$. Then there is a continuous function $f : \mathbb R^3 \to \mathbb R$ which takes the value $1$ at every point of $K$ and the value $0$ at every point outside $O$. This is the Urysohn construction applied to the pair $(K, O^c)$: the set $K$ is compact, the set $O^c$ is closed because $O$ is open, and the two are disjoint because $K \subseteq O$. Such a function is the device used to localise a small perturbation of the identity to a neighbourhood of a moving circle, so that a motion of one circle leaves the others exactly fixed.

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-!
# A continuous cutoff on `Space3`, equal to one on a compact set and zero off an open set

The ambient extension step of the round-circle motion needs, for a compact set `K`
inside an open set `O`, a function that is one on `K` and zero off `O`, used to cut off
the perturbation of the identity near a moving circle. This is the Urysohn construction
specialised to the pair `(K, Oᶜ)`: `K` is compact, `Oᶜ` is closed because `O` is open,
and they are disjoint because `K ⊆ O`. The instance chain needed is available on
`Space3 = Fin 3 → ℝ` automatically: `Function.compactSpace` gives `CompactSpace`,
`proper_of_compact` gives `ProperSpace`, `locallyCompact_of_proper` gives
`LocallyCompactSpace`, and a Hausdorff space is `RegularSpace`.
-/

namespace BookSixth

/-- Given a compact set `K` inside an open set `O` of `Space3`, there is a continuous
real-valued function equal to `1` on `K` and to `0` outside `O`. -/
theorem continuous_cutoff {K O : Set Space3} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ f : Space3 → ℝ, Continuous f ∧
      (∀ x, x ∈ K → f x = 1) ∧ (∀ x, x ∉ O → f x = 0) := by
  have hTc : IsClosed (Set.compl O) := hO.isClosed_compl
  have hKd : Disjoint K (Set.compl O) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxK
    intro hxO
    exact False.elim (hxO (hKO hxK))
  obtain ⟨f, hf0, hf1, _⟩ :=
    exists_continuous_zero_one_of_isCompact' hK hTc hKd
  exact ⟨(f : Space3 → ℝ), f.continuous, fun x hx => hf1 hx, fun x hxO => hf0 hxO⟩

end BookSixth


