-- Prove2me | Definitions.Def_Couret_STAT_TRANS_06_AdversarialCases_e73cf4a1e1dc
-- name    : Couret_STAT_TRANS_06_AdversarialCases_e73cf4a1e1dc
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:58.98343+00:00
-- url     : https://prove2.me/theorems/4b8e5487-954d-4c4a-8ae8-b656736883a2
-- title:
--   Bounded path oracle and explicit policy-test graphs
-- statement:
--   Defines a Boolean walk oracle on a list of typed dependency edges, an impact axis and natural fuel. At fuel zero it accepts only equal endpoints; with successor fuel it also accepts a permitted outgoing edge followed by a shorter accepted walk. It then defines explicit tiny graph lists: a documentary barrier between proof edges, a replay bridge, an unrelated cycle, and G30, T16, Cayley and OAI case encodings. The case names label policy-test data. Bounded walk is an executable test and does not by definition identify arbitrary unbounded reachability or certify the scientific claims named by nodes.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_06_AdversarialCases.lean; source file SHA-256 20b6292d6d043a85b3229ffe64c504f69f5c21240583c269d077c13cced07471

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_05_MutationSuite_39e36fa4811a

/-!
# STAT-TRANS-06 — Adversarial matrix and scientific case encodings

Finite, executable mutation oracles. These assertions test the current policy,
not the truth of any scientific claim. A bounded walk is not a formal
replacement for arbitrary Reach; positive Reach witnesses are established
in STAT_TRANS_05, and these oracles test negative paths on tiny graphs.

No RH claim. No external novelty claim. No publication-status promotion.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace AdversarialCases

open MutationSuite



/-- Bounded executable path oracle; zero steps still permits reflexivity. -/
def walk (es : List (TypedEdge Node)) (axis : ImpactAxis)
    (fuel : Nat) (src dst : Node) : Bool :=
  match fuel with
  | 0 => decide (src = dst)
  | n + 1 =>
      decide (src = dst) ||
        es.any (fun e =>
          decide (e.source = src) &&
          permits axis e.kind &&
          walk es axis n e.target dst)

/-! Mixed graph from STAT-TRANS-05: A -> B proof, A -> C replay,
    B -> D novelty, C -> D documentary. -/





/-- A documentary edge between two admissible proof edges blocks all axes. -/
def documentaryBarrier : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .proof },
   { source := .B, target := .C, kind := .documentary },
   { source := .C, target := .D, kind := .proof }]



/-- Mixed path: replay travels through proof -> replay -> proof, but
    neither semantic nor novelty may traverse the middle replay edge. -/
def replayBridge : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .proof },
   { source := .B, target := .C, kind := .replay },
   { source := .C, target := .D, kind := .proof }]



/-- An unrelated cycle cannot generate a false positive at a disconnected D. -/
def unrelatedCycle : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .proof },
   { source := .B, target := .C, kind := .proof },
   { source := .C, target := .A, kind := .proof }]





/-! G30: A finite certificate, B a local derived statement, C an
    unsupported global extension, D a documentary pointer to C.
    There is intentionally no proof bridge to C. -/
def g30Case : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .proof },
   { source := .B, target := .C, kind := .documentary },
   { source := .C, target := .D, kind := .documentary }]



/-! T16: A abstract equivalence theorem, B fixed-modulus
    instantiation, C derived mathematical claim, D novelty audit. -/
def t16Case : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .proof },
   { source := .B, target := .C, kind := .proof },
   { source := .C, target := .D, kind := .novelty }]



/-! Cayley: A primary prior-art result, B originality review,
    C public review document, D independently audited mathematical
    proof. Only the bibliographic channel A -> B is licensed. -/
def cayleyCase : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .novelty },
   { source := .B, target := .C, kind := .documentary }]



/-! OAI-7/8: A verifier/toolchain, B replay result,
    C published narrative, D bibliographic originality.
    A comparison pass is not a novelty or publication certificate. -/
def oaiCase : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .replay },
   { source := .B, target := .C, kind := .documentary }]





end AdversarialCases
end StatusTransport
end CouretOaiBridge01


