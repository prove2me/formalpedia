-- Prove2me | Definitions.Def_Logic_AlmostLossless_Core
-- name    : Logic_AlmostLossless_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:46:12.146481+00:00
-- url     : https://prove2.me/theorems/95e72d1d-811d-40de-bb58-c8ed5a6f12d1
-- title:
--   Aether Catalog definitions — Logic_AlmostLossless_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AlmostLossless.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AlmostLossless/Core.lean by skeleton subtraction
import Mathlib

/-!
# Almost-lossless compression: the ε-relaxed counting bound

This file is the foundation of a small formal theory of *almost-lossless*
(one-shot, fixed-length) source compression.  The guiding question is the one
from the research thread *Compression Beyond the Pigeonhole Bound*:

> Pigeonhole governs exact decoding of **all** strings.  If we only ask that the
> decoder succeed with probability `≥ 1 - ε`, how far does the counting bound
> relax, and can a random number generator (shared randomness) help?

## Contents

* `AlmostLossless.Code` : an encoder/decoder pair `S → C → Option S`.
* `AlmostLossless.Honest` : *no silent corruption* — on every source word the
  decoder either returns the correct word or explicitly declares failure.
* `AlmostLossless.card_correct_le_card_code` : the pigeonhole core, the set of
  correctly decoded words injects into the code alphabet.
* `AlmostLossless.uniform_failProb_lower` : for a uniform source the failure
  probability is at least `1 - |C|/|S|`; equivalently
  `AlmostLossless.card_code_ge_of_failProb_le` : an `ε`-reliable code needs
  `|C| ≥ (1-ε)|S|`.  This is *exactly* how much the counting bound relaxes.
* `AlmostLossless.randomized_avg_failProb_lower` : the same bound holds for the
  average failure probability of an arbitrary **randomized** ensemble of codes,
  i.e. a random number generator buys nothing at all on a uniform source.
* `AlmostLossless.tableCode` and `AlmostLossless.failProb_tableCode_le` : the
  matching achievability statement.  Any *typical set* `T` of probability
  `≥ 1 - ε` yields an honest code with alphabet of size `|T| + 1` and failure
  probability `≤ ε`, with `O(1)` (single table lookup) decoding.

Everything is finite and rational-valued: probabilities are explicit finite
sums, so all statements are elementary and fully constructive in content.
-/

namespace AlmostLossless

open Finset

/-- A fixed-length code: an encoder `enc : S → C` together with a decoder
`dec : C → Option S`, where `none` is an explicit *decoding failure* symbol. -/
structure Code (S C : Type*) where
  /-- The encoder. -/
  enc : S → C
  /-- The decoder; `none` means "I refuse to decode". -/
  dec : C → Option S

variable {S C : Type*}

/-- The source word `s` is decoded correctly. -/
def Correct (K : Code S C) (s : S) : Prop := K.dec (K.enc s) = some s

instance [DecidableEq S] (K : Code S C) (s : S) : Decidable (Correct K s) := by
  unfold Correct; infer_instance

/-- **No silent corruption**: on every source word the decoder either returns
the true word or explicitly aborts.  It never returns a *wrong* word. -/
def Honest (K : Code S C) : Prop :=
  ∀ s, K.dec (K.enc s) = some s ∨ K.dec (K.enc s) = none


/-! ## The pigeonhole core -/



/-! ## Sources and failure probability -/

/-- A finitely supported probability distribution with rational weights. -/
structure Source (S : Type*) [Fintype S] where
  /-- The probability weight of each source word. -/
  w : S → ℚ
  /-- Weights are nonnegative. -/
  nonneg : ∀ s, 0 ≤ w s
  /-- Weights sum to one. -/
  total : ∑ s, w s = 1

variable [Fintype S]

/-- Probability of an event (a finite set of source words). -/
def Source.prob (μ : Source S) (A : Finset S) : ℚ := ∑ s ∈ A, μ.w s

/-- The probability that the decoder does **not** return the true source word. -/
def failProb [DecidableEq S] (μ : Source S) (K : Code S C) : ℚ :=
  ∑ s ∈ ({s | ¬ Correct K s} : Finset S), μ.w s




/-- The uniform source on a nonempty finite alphabet. -/
def uniformSource [Nonempty S] : Source S where
  w _ := (Fintype.card S : ℚ)⁻¹
  nonneg _ := by positivity
  total := by
    have h : (Fintype.card S : ℚ) ≠ 0 := by
      have := Fintype.card_pos (α := S); positivity
    simp [Finset.sum_const, Finset.card_univ]

/-! ## The ε-relaxed counting bound (converse) -/



/-! ## Randomness does not help on a uniform source -/

/-- Average failure probability of a randomized ensemble of codes indexed by a
uniformly random seed `ω : Ω` (shared randomness / a common RNG). -/
def avgFailProb [DecidableEq S] {Ω : Type*} [Fintype Ω] (μ : Source S)
    (K : Ω → Code S C) : ℚ :=
  (∑ ω, failProb μ (K ω)) / (Fintype.card Ω : ℚ)



/-! ## Achievability: the typical-set table code -/

/-- The **table code** for a typical set `T`: enumerate `T` and send the index,
sending the explicit failure symbol `none` for every atypical word. -/
noncomputable def tableCode [DecidableEq S] (T : Finset S) : Code S (Option (Fin T.card)) where
  enc s := if h : s ∈ T then some (T.equivFin ⟨s, h⟩) else none
  dec o := o.map (fun i => (T.equivFin.symm i : S))





/-! ## The exact ε-relaxed pigeonhole principle -/


/-- Transport a code along an injection of the code alphabet. -/
noncomputable def spreadCode [DecidableEq S] [DecidableEq C] (T : Finset S)
    (f : Fin T.card ↪ C) (c₀ : C) : Code S C where
  enc s := if h : s ∈ T then f (T.equivFin ⟨s, h⟩) else c₀
  dec c := if h : ∃ i : Fin T.card, f i = c then some (T.equivFin.symm h.choose) else none



end AlmostLossless


