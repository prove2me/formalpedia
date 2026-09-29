-- Prove2me | Definitions.Def_Evergreen_RudyRucker_CantorsParadise
-- name    : Evergreen_RudyRucker_CantorsParadise
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:30:15.130624+00:00
-- url     : https://prove2.me/theorems/ef9744db-6b51-419d-ad1f-e77685d0beb0
-- title:
--   Aether Catalog definitions — Evergreen_RudyRucker_CantorsParadise
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.RudyRucker.CantorsParadise`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/RudyRucker/CantorsParadise.lean by skeleton subtraction
import Mathlib
/-
# Cantor's Paradise: Formalizing the Hierarchy of Infinities

Rudy Rucker's "Infinity and the Mind" (1982) is a landmark exploration of
transfinite mathematics. Rucker, a mathematician and novelist, brought Cantor's
paradise to life for a broad audience. This module formalizes key results from
Cantor's theory of transfinite numbers that form the backbone of Rucker's
mathematical philosophy.

## Key Themes from Rucker:
- "The Absolute Infinite is unknowable" — but we can still reason about
  ever-larger infinities.
- The diagonal argument is "the most beautiful proof in mathematics."
- There is no "biggest" infinity — the power set always produces something larger.
-/


open Cardinal

namespace CantorsParadise

/-! ## Cantor's Theorem: The Power Set is Always Strictly Larger

Rucker emphasizes that Cantor's 1891 diagonal argument is one of the most
profound discoveries in mathematics. It shows that for ANY set S, the collection
of all subsets of S (its power set) is strictly larger than S itself.

This is the engine that generates the infinite hierarchy of infinities:
ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ...
-/


/-- The diagonal set used in Cantor's proof: the set of all elements
that are NOT in their own image. This is the formal "Cantorian diagonal"
that Rucker describes as the key to understanding infinity. -/
def cantor_diagonal {α : Type*} (f : α → Set α) : Set α :=
  {x | x ∉ f x}


/-! ## The Hierarchy of Cardinals

Rucker describes how Cantor discovered an endless ascending chain of
infinities. We formalize this using Mathlib's cardinal arithmetic. -/




/-! ## The Schröder–Bernstein Theorem

Rucker discusses how comparing infinite sets requires care. The
Schröder–Bernstein theorem tells us that if A injects into B and
B injects into A, then A and B have the same cardinality. -/


/-! ## Countability and Uncountability

Central to Rucker's exposition is the distinction between countable and
uncountable infinities. -/




end CantorsParadise


