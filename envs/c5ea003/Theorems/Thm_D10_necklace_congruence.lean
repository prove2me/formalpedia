-- Prove2me | Theorems.Thm_D10_necklace_congruence
-- name    : D10.necklace_congruence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:27:11.057842+00:00
-- url     : https://prove2.me/theorems/ab631977-40e0-4eb0-939e-244b1fdb2515
-- title:
--   Necklace congruence (a Gauss-type congruence): for every `n ≥ 1` and every number of
-- statement:
--   **Necklace congruence** (a Gauss-type congruence): for every `n ≥ 1` and every number of
--   colours `k`, `n` divides `∑_{a ∈ ℤ/n} k ^ gcd(n, a)`.
--
--   ```lean
--   theorem D10.necklace_congruence(k : ℕ) :
--       n ∣ ∑ a : ZMod n, k ^ Nat.gcd n a.val := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MolienNecklaceCongruence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MolienNecklaceCongruence.lean#L176

-- Thm stub generated from NumberTheory/MolienNecklaceCongruence.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienNecklaceCongruence

/-!
# The Molien/Burnside machinery as an arithmetic engine: necklace congruences

This file is the number-theoretic pay-off of the Molien/Burnside framework of
`Catalog.NumberTheory.MolienBurnsideD10`.  The bridge is the *cycle-index* identity

`|X^g| = k ^ (number of ⟨g⟩-orbits on Y)`   for `X = Coloring Y k = (Y → Fin k)`,

proved here as `D10.Coloring.fixCount_coloring`.  Feeding it into the Burnside divisibility
`|G| ∣ ∑_{g ∈ G} |X^g|` for the rotation action of `ℤ/n` on itself yields the classical
**necklace congruence**

`n ∣ ∑_{a ∈ ℤ/n} k ^ gcd(n, a)`,

and, specialising to a prime, **Fermat's little theorem** `k^p ≡ k (mod p)`.  Thus the
Molien invariant, which the Klein four-group example of the companion file shows to be a
*strictly coarser* invariant than the Burnside mark vector, is nevertheless strong enough
to carry genuine arithmetic content.
-/

open D10

open Finset MulAction


open Coloring

variable {G Y : Type*} [Group G] [MulAction G Y] {k : ℕ}



instance : SMul G (Coloring Y k) := ⟨fun g f => (fun y => f (g⁻¹ • y) : Y → Fin k)⟩









variable {n : ℕ} [NeZero n]

theorem D10.necklace_congruence(k : ℕ) :
    n ∣ ∑ a : ZMod n, k ^ Nat.gcd n a.val := by sorry
