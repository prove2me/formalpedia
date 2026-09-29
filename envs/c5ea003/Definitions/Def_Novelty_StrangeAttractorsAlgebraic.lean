-- Prove2me | Definitions.Def_Novelty_StrangeAttractorsAlgebraic
-- name    : Novelty_StrangeAttractorsAlgebraic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:42:26.087718+00:00
-- url     : https://prove2.me/theorems/130bf0f2-72e9-45b3-a51d-7ee182ef0fb3
-- title:
--   Aether Catalog definitions — Novelty_StrangeAttractorsAlgebraic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StrangeAttractorsAlgebraic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StrangeAttractorsAlgebraic.lean by skeleton subtraction
import Mathlib

/-!
# Finite graph approximants and a Cantor inverse limit

Binary de Bruijn graphs give a concrete finite directed-graph model for symbolic
dynamics.  Vertices at level `n` are binary words of length `n + 1`; an edge
records a one-symbol left shift.  Deleting the final symbol is a bonding map of
directed graphs.  Compatible finite prefixes form an inverse limit, and every
infinite binary stream determines a distinct point of that limit.
-/

namespace StrangeAttractorsAlgebraic

/-- Binary words of length `n`. -/
abbrev Word (n : ℕ) := Fin n → Bool

/-- Delete the final symbol of a binary word. -/
def truncate (n : ℕ) (w : Word (n + 1)) : Word n :=
  fun i => w ⟨i, Nat.lt_succ_of_lt i.isLt⟩

/-- The edge relation of the binary de Bruijn graph of order `n + 1`.
There is an edge from `u` to `v` when the final `n` symbols of `u` are the
initial `n` symbols of `v`. -/
def deBruijnEdge (n : ℕ) (u v : Word (n + 1)) : Prop :=
  ∀ i : Fin n,
    u ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
      v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩



/-- The inverse limit of the finite binary-prefix diagram. -/
def PrefixLimit :=
  {x : ∀ n, Word n // ∀ n, truncate n (x (n + 1)) = x n}

/-- The compatible family of finite prefixes of an infinite binary stream. -/
def streamToLimit (s : ℕ → Bool) : PrefixLimit :=
  ⟨fun n i => s i, by
    intro n
    funext i
    rfl⟩



end StrangeAttractorsAlgebraic


