-- Prove2me | Definitions.Def_Probability_SelfModifyingUndecidability
-- name    : Probability_SelfModifyingUndecidability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:28.444186+00:00
-- url     : https://prove2.me/theorems/bc93ab6d-88ad-4cfc-8adb-61d53403a334
-- title:
--   Aether Catalog definitions — Probability_SelfModifyingUndecidability
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SelfModifyingUndecidability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SelfModifyingUndecidability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_SelfModHalt
/-!
# Self-Modification, Halting, and Semantic Monitoring

A machine that rewrites its current program can be simulated by a fixed program
whose state stores the changing code. Consequently, unrestricted
self-modification does not create a degree of undecidability above the classical
halting problem: the two termination questions are mutually reducible. What
survives is the classical obstruction itself—there is no general termination
predictor—and Rice's theorem rules out sound-and-complete monitors for every
nontrivial extensional behavioral property.

The results also isolate the boundary relevant to malware detection and safety
monitoring. Bounded execution questions remain decidable, while an exact monitor
for an unbounded temporal property would decide halting or its complement.

-- !-- Lab Notes -- !--

* Hypothesis (Hypothesizer, ranked by impact): (1) self-modifying halting is
  strictly harder than classical halting; (2) no computable total predictor
  recognizes termination of every program; (3) every nontrivial extensional
  malware property defeats exact computable detection; (4) exact perpetual
  safety monitoring is as impossible as termination prediction; (5) bounded
  self-modification creates a strict hierarchy; (6) oracle-assisted rewriting
  follows the jump hierarchy. The first, fifth, and sixth are the boldest
  structural claims.
* Experiment (Experimenter): The changing program was paired with the ordinary
  machine state. Induction on execution length gives step-for-step simulation,
  and both halting predicates reduce to one another. Classical indexed partial
  computation was then used to test the universal-predictor claim, while
  extensional program properties were tested against Rice's theorem.
* Analysis (Analyst): Conjecture (1) is false for ordinary effective
  self-modification: code is data, so a fixed interpreter absorbs every rewrite.
  Conjectures (2)--(4) survive. Conjecture (5) needs a resource-sensitive
  complexity notion rather than computability degree; conjecture (6) needs an
  explicit oracle model. The unifying pattern is that rewriting changes
  operational presentation but not extensional computability power.
* Critique (Critic): Mutual reducibility must not be confused with pointwise
  equality, and an arbitrary transition system is not automatically universal.
  The unconditional undecidability theorem therefore uses the standard
  universal partial evaluator; results for a particular self-modifying machine
  explicitly assume undecidability of its fixed-state simulation. No claim of
  strict hardness remains. The semantic detector theorem requires both
  extensionality and nontriviality; dropping either condition admits easy
  classifiers.
* Synthesis (Principal Investigator): Exact run simulation refutes strictness,
  classical diagonal undecidability excludes universal termination prediction,
  complement closure excludes exact perpetual-safety monitors, and Rice's
  theorem supplies the virus-detection and behavioral-alignment obstruction.
-/

namespace SelfModifyingUndecidability

open Nat.Partrec
open Nat.Partrec.Code
open SelfModHalt

/-- Predicate `A` is strictly harder than `B` when `B` reduces to `A` but `A`
does not reduce back to `B`. -/
def StrictlyHarder {α β : Sort*} (A : α → Prop) (B : β → Prop) : Prop :=
  ManyOneReduces B A ∧ ¬ ManyOneReduces A B

/-
Ordinary self-modification is not strictly harder than fixed-program
computation. Every changing-code run is simulated by storing code in the state;
the reverse direction embeds a fixed machine using a one-element program type.
-/

/-
No computable Boolean function predicts termination of every indexed
partial recursive program on a fixed input.
-/

/-- A configuration is perpetually safe from halting when every finite run is
still defined. -/
def NeverHalts {P S : Type*} (m : SelfModMachine P S)
    (cfg : SelfModConfig P S) : Prop :=
  ∀ n, m.run cfg n ≠ Option.none

/-
Perpetual safety is exactly the complement of eventual halting.
-/

/-
If the fixed-state simulation has no halting decider, then there is no exact
Boolean monitor for perpetual safety of the self-modifying machine.
-/

/-
Rice-style virus and alignment obstruction: a behavioral property containing
one partial-recursive behavior but excluding another has no exact computable
classifier on program codes.
-/

/-
In particular, even perpetual nontermination at one input is not recursively
enumerable; finite observation can confirm halting but cannot in general certify
that execution will continue forever.
-/

end SelfModifyingUndecidability


