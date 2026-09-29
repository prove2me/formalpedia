-- Prove2me | Definitions.Def_Applications_SelbergCensus_Dirichlet
-- name    : Applications_SelbergCensus_Dirichlet
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:47.299633+00:00
-- url     : https://prove2.me/theorems/dfa2f763-a645-4436-89eb-91a44ff8436b
-- title:
--   Aether Catalog definitions — Applications_SelbergCensus_Dirichlet
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SelbergCensus.Dirichlet`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SelbergCensus/Dirichlet.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dirichlet L-functions: the degree-one stratum of the census

The simplest infinite family of L-functions beyond the Riemann zeta function is
the family of **Dirichlet L-functions** `L(s, χ) = ∑ₙ χ(n) n⁻ˢ`, one for each
Dirichlet character `χ` modulo `n`.  In Lean/Mathlib a Dirichlet character mod
`n` valued in `ℂ` is `DirichletCharacter ℂ n = MulChar (ZMod n) ℂ`.

This file quantifies "how many Dirichlet L-functions there are":

* `dirichlet_finite_mod` — for each modulus `n ≥ 1` there are only **finitely
  many** Dirichlet characters;
* `dirichlet_family_countable` — the family of **all** Dirichlet characters, over
  all moduli, is **countable**;
* `dirichlet_family_infinite` — it is nevertheless **infinite** (an explicit
  injection via principal characters of growing modulus);
* `dirichlet_family_countably_infinite` — packaging the two: the Dirichlet
  L-functions are exactly as numerous as `ℕ`.

This is the concrete, fully verified confirmation of point (2) of the census:
*Dirichlet L-functions are countable.*

The file is self-contained and imports only Mathlib.
-/

namespace SelbergCensus

open scoped Classical



/-- The principal (trivial) Dirichlet character of modulus `n + 1`, bundled with
its modulus.  As `n` varies this produces infinitely many *distinct* Dirichlet
characters, because the modulus `n + 1` is strictly increasing. -/
noncomputable def principalFamily (n : ℕ) : Σ m : ℕ, DirichletCharacter ℂ m :=
  ⟨n + 1, (1 : DirichletCharacter ℂ (n + 1))⟩




end SelbergCensus


