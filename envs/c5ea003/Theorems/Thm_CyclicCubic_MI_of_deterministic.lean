-- Prove2me | Theorems.Thm_CyclicCubic_MI_of_deterministic
-- name    : CyclicCubic.MI_of_deterministic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:33:54.303421+00:00
-- url     : https://prove2.me/theorems/127fc100-3901-4612-b464-02c475be26b2
-- title:
--   Determinism saturates the ceiling.
-- statement:
--   **Determinism saturates the ceiling.**  If the second coordinate is the
--   value of a function `g` of the first, the mutual information equals the full
--   entropy of the second marginal.
--
--   ```lean
--   theorem CyclicCubic.MI_of_deterministic[DecidableEq β] (g : α → β) (v : α → ℝ) :
--       MI (fun q : α × β => if q.2 = g q.1 then v q.1 else 0)
--         = H univ (fun b : β => ∑ a : α, if b = g a then v a else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/CyclicCubicTypeChannel/ChannelBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/CyclicCubicTypeChannel/ChannelBounds.lean#L75

-- Thm stub generated from Applications/CyclicCubicTypeChannel/ChannelBounds.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Entropy
import Definitions.Def_Applications_LabelEntropyDeficit
/-
# Why the cyclic-cubic channel is *fully* pinned: the structural reason

## Context (FACT round-32 #3, cycle 3)

`Applications.CyclicCubicTypeChannel.Entropy` computes, for the conductor-`7`
cyclic cubic field, the exact identity `I(p mod 7 ; T) = H(T)`.  Taken alone
that is a numerical coincidence of two closed forms.  This file explains it.

Two general facts about an arbitrary finite joint distribution `w : α × β → ℝ`
are proved from the entropy deficit of `Applications.LabelEntropyDeficit`:

* `CyclicCubic.MI_le_left` / `CyclicCubic.MI_le_right` — the *data-processing
  ceiling* `I(X;Y) ≤ H(X)` and `I(X;Y) ≤ H(Y)`, a consequence of
  `LabelEntropy.nlp_sum_le_H` (merging labels loses entropy) applied fibrewise;
* `CyclicCubic.MI_of_deterministic` — if the second coordinate is a *function*
  of the first, the ceiling is attained: `I(X;Y) = H(Y)`.

Specialising the second statement to the splitting-type map `resType` gives
`CyclicCubic.full_pinning_structural`, a second and conceptual proof of full
pinning: the type is pinned because the splitting law
`p ≡ ±1 (mod 7) ↔ deg = 1` is a *deterministic* function of `p mod 7`, not
because two logarithms happen to agree.

Finally `CyclicCubic.semiprime_deficit_eq_type_entropy` measures the failure for
semiprimes in the same currency: the gap between the ceiling `H(pair)` and the
transmitted information `I` is *exactly* `H(T)`, one full type's worth of
entropy — the multiplicative structure destroys precisely one factor's label.
-/

open Finset LabelEntropy

open CyclicCubic

/-! ## General upper bounds on mutual information -/


variable {α β : Type*} [Fintype α] [Fintype β]

theorem CyclicCubic.MI_of_deterministic[DecidableEq β] (g : α → β) (v : α → ℝ) :
    MI (fun q : α × β => if q.2 = g q.1 then v q.1 else 0)
      = H univ (fun b : β => ∑ a : α, if b = g a then v a else 0) := by sorry
