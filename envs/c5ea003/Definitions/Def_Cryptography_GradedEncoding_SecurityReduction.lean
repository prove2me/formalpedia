-- Prove2me | Definitions.Def_Cryptography_GradedEncoding_SecurityReduction
-- name    : Cryptography_GradedEncoding_SecurityReduction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:41:20.005528+00:00
-- url     : https://prove2.me/theorems/4cfef008-b03f-4da9-acae-cec394f76f11
-- title:
--   Aether Catalog definitions — Cryptography_GradedEncoding_SecurityReduction
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.GradedEncoding.SecurityReduction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/GradedEncoding/SecurityReduction.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_GradedEncoding_Foundations
import Definitions.Def_Cryptography_LWE_OperationalSecurity

/-!
# Security reductions for multilinear graded encodings

The reduction layer is independent of any particular graded-encoding candidate.
A decisional multilinear Diffie--Hellman game is represented by its two finite
transcript distributions. A perfect reduction is an equivalence of transcript
spaces preserving both distributions pointwise. The main theorem proves exact
preservation of every deterministic distinguisher's advantage and transfers any
source hardness bound to the graded target game.
-/

open Finset

noncomputable section

namespace Cryptography.GradedEncoding

/-- A finite two-world decisional game. `false` is the random world and `true`
is the real multilinear Diffie--Hellman world. -/
structure DecisionGame (Ω : Type*) [Fintype Ω] where
  experiment : LWEOperational.EncryptionExperiment Ω

namespace DecisionGame

variable {Ω : Type*} [Fintype Ω]

/-- Acceptance probability of a deterministic distinguisher in one world. -/
def acceptance (G : DecisionGame Ω) (b : Bool) (A : Ω → Bool) : ℝ :=
  ∑ x with A x = true, (G.experiment.challenge b).mass x

/-- Absolute distinguishing advantage. -/
def advantage (G : DecisionGame Ω) (A : Ω → Bool) : ℝ :=
  |G.acceptance true A - G.acceptance false A|


end DecisionGame

variable {Source Target : Type*} [Fintype Source] [Fintype Target]

/-- A perfect, lossless reduction between finite decisional games. The transcript
equivalence is executable, while `mass_preserving` states exact simulation of
both challenge worlds. -/
structure PerfectReduction (source : DecisionGame Source)
    (target : DecisionGame Target) where
  transcriptEquiv : Source ≃ Target
  mass_preserving : ∀ (b : Bool) (x : Source),
    (target.experiment.challenge b).mass (transcriptEquiv x) =
      (source.experiment.challenge b).mass x

namespace PerfectReduction

variable {source : DecisionGame Source} {target : DecisionGame Target}

/-- Turn a target-game distinguisher into a source-game distinguisher. -/
def reduce (red : PerfectReduction source target) (A : Target → Bool) : Source → Bool :=
  A ∘ red.transcriptEquiv





end PerfectReduction

namespace DecisionGame



end DecisionGame
end Cryptography.GradedEncoding

end


