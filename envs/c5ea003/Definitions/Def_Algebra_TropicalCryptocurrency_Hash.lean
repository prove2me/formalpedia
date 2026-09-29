-- Prove2me | Definitions.Def_Algebra_TropicalCryptocurrency_Hash
-- name    : Algebra_TropicalCryptocurrency_Hash
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:15:22.534952+00:00
-- url     : https://prove2.me/theorems/af10d511-fbad-4bd7-81ae-dfacd31583fb
-- title:
--   Aether Catalog definitions — Algebra_TropicalCryptocurrency_Hash
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalCryptocurrency.Hash`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalCryptocurrency/Hash.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Cryptocurrency: Exact Preimages and Universal Collisions

For a nonempty finite message vector, the min-plus hash is
`min i, (m i + h i)`.  The results below test two proposed security claims.
The first hash has an explicit preimage for every output.  More strongly, adding
one coordinate while retaining a different minimizing coordinate preserves the
hash.  Applying this observation to both components proves that every two-key
hash in dimension at least three has a collision, for every pair of keys and
every starting message.

The target serves the cross-domain category: finite min-plus algebra is connected
to preimage search, collision resistance, and optimization certificates.

-- !-- Lab Notes -- !--
Hypothesis: Seven falsifiable targets were ranked by expected impact: (1) a
nonce-constrained tropical inversion problem is NP-complete (P versus NP
subtask); (2) bounded-alphabet inversion has a sharp complexity transition (P
versus NP subtask); (3) nonlinear tropical circuits yield average-case one-way
families (P versus NP subtask); (4) approximation of constrained inversion has a
hardness threshold (P versus NP subtask); (5) two independent linear tropical
keys are collision-resistant (algebra--cryptography bridge); (6) hash fibers are
polyhedral complexes (algebra--geometry bridge); and (7) tropical mining is
equivalent to shortest-path search (algebra--optimization bridge).
Experiment: The unrestricted fiber equation underlying targets (5) and (7) was
reduced to coordinate inequalities plus one active equality.  A canonical
preimage was then constructed.  For two keys, a minimizing coordinate was
selected for each component and a third coordinate was increased.
Analysis: Preimage search does not encode a shortest-path problem in this model:
`m i = y - h i` is an explicit preimage.  Two keys do not repair collisions.
Each component needs only one unchanged minimizer, so two components protect at
most two coordinates.
Critique: The collision theorem is deterministic, not probabilistic, and permits
unrestricted real messages.  Bounded alphabets or nonce-constrained message
families could behave differently and require separate analysis.  The theorem
does not assert a computational lower bound; it establishes algebraic
non-injectivity directly.
Synthesis: Tropical fibers admit exact certificates, every output is attained,
and an r-component min-plus hash remains universally collision-prone whenever
there is a coordinate outside the chosen r minimizers.  The two-component case
is proved here for all dimensions at least three.
-- !-- end Lab Notes -- !--
-/

noncomputable section

namespace TropicalCryptocurrency

/-- The min-plus hash of a finite real message under a real key. -/
def tsha {k : ℕ} [Nonempty (Fin k)] (h m : Fin k → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => m i + h i)

/-- The two-key min-plus hash. -/
def tsha2 {k : ℕ} [Nonempty (Fin k)] (h h' m : Fin k → ℝ) : ℝ × ℝ :=
  (tsha h m, tsha h' m)









end TropicalCryptocurrency


