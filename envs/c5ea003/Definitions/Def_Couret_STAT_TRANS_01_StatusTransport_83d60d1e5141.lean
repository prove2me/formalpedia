-- Prove2me | Definitions.Def_Couret_STAT_TRANS_01_StatusTransport_83d60d1e5141
-- name    : Couret_STAT_TRANS_01_StatusTransport_83d60d1e5141
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:11.993987+00:00
-- url     : https://prove2.me/theorems/e6771974-cc80-43a5-85cb-6843e89ab4be
-- title:
--   Scoped claims and conservative transport witnesses
-- statement:
--   For any type $\alpha$, a claim is a pair $(S,P)$ with scope $S\subseteq\alpha$ and predicate $P:\alpha\to\mathrm{Prop}$. It holds when $P(x)$ is true for every $x\in S$. A transport from $(S,P)$ to $(T,Q)$ carries both witnesses $$T\subseteq S,\qquad\forall x\in T,\ P(x)\Longrightarrow Q(x).$$ This interface exposes the scope-inclusion and predicate-bridge obligations explicitly. Empty scopes are allowed. It provides conservative transport within the model and does not assert that a wider mathematical claim could never be proved by another argument.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_01_StatusTransport.lean; source file SHA-256 ee5a7b8aec759c0299316042f25743e7f347a3b6c75a56ffa45fec786dc899da

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic

/-!
# STAT-TRANS-01 — Minimal status-transport kernel

This file formalizes only the semantic core needed for scope transport.

A claim consists of a scope and a predicate. A transport from a source claim
to a target claim must explicitly carry a proof that every target point lies
in the source scope and a pointwise bridge from source predicate to target.

Thus the API exposes no constructor for scope widening without an explicit
witness. This is governance by construction, not a theorem that no external
mathematical proof of a wider claim could exist.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport

/-- A scoped mathematical claim. -/
structure Claim (α : Type*) where
  scope : Set α
  pred : α → Prop

/-- The claim holds everywhere on its declared scope. -/
def Holds {α : Type*} (C : Claim α) : Prop :=
  ∀ x, x ∈ C.scope → C.pred x

/-- A certified conservative transport from source to target. -/
structure Transport {α : Type*} (source target : Claim α) where
  scope_le : target.scope ⊆ source.scope
  bridge : ∀ x, x ∈ target.scope → source.pred x → target.pred x















end StatusTransport
end CouretOaiBridge01


