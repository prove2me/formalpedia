-- Prove2me | Definitions.Def_Couret_STAT_TRANS_05_MutationSuite_39e36fa4811a
-- name    : Couret_STAT_TRANS_05_MutationSuite_39e36fa4811a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:37.172594+00:00
-- url     : https://prove2.me/theorems/e0c354d1-f48a-43c5-9511-71c64f6d6090
-- title:
--   A fixed four-node typed-dependency mutation fixture
-- statement:
--   In StatusTransport.MutationSuite, Node has exactly A,B,C,D. The bundle defines a proof edge A→B, replay edge A→C, novelty edge B→D, documentary edge C→D, and their ordered list. Three one-element mutation lists seed node A with, respectively, semanticChanged, dependenciesChanged, or noveltyChanged set to true; all other Delta flags retain their false defaults. These are synthetic input fixtures. The bundle itself contains no acceptance/rejection or reachability theorem and makes no assertion about a scientific application graph.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_05_MutationSuite.lean; source file SHA-256 62a8f58f0372313f9ba80d9a0dfb97d452fe508070b154c884b1a452a7b7e23f

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_04_TypedDependencies_3df632007942

/-!
# STAT-TRANS-05 — Pre-specified mutation suite

This file freezes a small synthetic graph before application to G30, T16,
Cayley, or OAI-7/8.

The suite tests both accepted and rejected propagation channels.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace MutationSuite

inductive Node where
  | A
  | B
  | C
  | D
  deriving Repr, DecidableEq

def proofAB : TypedEdge Node :=
  { source := .A, target := .B, kind := .proof }

def replayAC : TypedEdge Node :=
  { source := .A, target := .C, kind := .replay }

def noveltyBD : TypedEdge Node :=
  { source := .B, target := .D, kind := .novelty }

def documentaryCD : TypedEdge Node :=
  { source := .C, target := .D, kind := .documentary }

def edges : List (TypedEdge Node) :=
  [proofAB, replayAC, noveltyBD, documentaryCD]

def semanticAtA : List (ChangeAt Node) :=
  [{ node := .A, delta := { semanticChanged := true } }]

def replayAtA : List (ChangeAt Node) :=
  [{ node := .A, delta := { dependenciesChanged := true } }]

def noveltyAtA : List (ChangeAt Node) :=
  [{ node := .A, delta := { noveltyChanged := true } }]

/-! ## Policy mutations: ACCEPT / REJECT -/

















/-! ## Local seed mutations -/







/-! ## Direct propagation mutations -/





/-! ## Multi-hop mutation -/



/-! ## Channel-separation mutations -/







end MutationSuite
end StatusTransport
end CouretOaiBridge01


