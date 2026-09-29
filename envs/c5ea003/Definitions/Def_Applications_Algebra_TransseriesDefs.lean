-- Prove2me | Definitions.Def_Applications_Algebra_TransseriesDefs
-- name    : Applications_Algebra_TransseriesDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:41.371526+00:00
-- url     : https://prove2.me/theorems/fc1d1051-067a-4952-a8bc-e844ab99e618
-- title:
--   Aether Catalog definitions — Applications_Algebra_TransseriesDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Algebra.TransseriesDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Algebra/TransseriesDefs.lean by skeleton subtraction
import Mathlib
/-
  # Transseries: Asymptotic Expansions Beyond Power Series

  We formalize a novel hierarchy of transseries — formal asymptotic expansions
  that extend classical power series by incorporating iterated exponentials
  and logarithms. The key mathematical insight: the asymptotic behavior of
  exp-log-monomial (EML) functions is captured by a well-ordered "level"
  structure that governs dominance among terms.

  ## Novel Structure: TransLevel and Transseries

  A `TransLevel` classifies the asymptotic growth rate of a monomial:
  - `Var` represents the identity function x
  - `Exp n` represents the n-fold iterated exponential exp^(n+1)(x)
  - `Log n` represents the n-fold iterated logarithm log^(n+1)(x)

  A `TransMonomial` pairs a level with a real exponent α, representing
  functions like x^α, exp(x)^α, log(log(x))^α.

  A `Transseries` is a finitely-supported formal sum of such monomials,
  providing a canonical asymptotic expansion for EML functions.
-/


namespace Transseries

/-! ## Level Structure

The `TransLevel` type classifies the asymptotic growth rate of monomials.
The key property: there is a natural total ordering on levels corresponding
to asymptotic dominance, where Exp levels dominate Var, which dominates Log levels.
-/

/-- A level in the transseries hierarchy, encoded as an integer.
  Negative values represent iterated logs, zero represents x,
  positive values represent iterated exponentials.
  E.g., -2 = log(log(x)), -1 = log(x), 0 = x, 1 = exp(x), 2 = exp(exp(x)). -/
def TransLevel := ℤ

instance : DecidableEq TransLevel := inferInstanceAs (DecidableEq ℤ)
instance : LinearOrder TransLevel := inferInstanceAs (LinearOrder ℤ)
instance : Add TransLevel := inferInstanceAs (Add ℤ)
instance : Neg TransLevel := inferInstanceAs (Neg ℤ)
instance : Zero TransLevel := inferInstanceAs (Zero ℤ)
instance : One TransLevel := inferInstanceAs (One ℤ)
instance : Repr TransLevel := inferInstanceAs (Repr ℤ)

namespace TransLevel








end TransLevel

/-! ## Trans-Monomials

A `TransMonomial` pairs a level with a real exponent α, representing
functions like x^α, exp(x)^β, log(log(x))^γ.
-/


namespace TransMonomial



end TransMonomial

/-! ## Transseries Expansion

A `TransseriesExpansion` is a list of (coefficient, monomial) pairs
in strictly decreasing dominance order. This provides the canonical
form for asymptotic expansions.
-/



namespace FormalTransseries












end FormalTransseries

/-! ## Well-ordering and Dominance Theorems -/




end Transseries


