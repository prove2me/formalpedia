-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_compensating_class_works
-- name    : Bridges.ResidueLeakage.compensating_class_works
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:30:59.745756+00:00
-- url     : https://prove2.me/theorems/b9c6055c-cdd2-4dd1-a924-d9f90ff2d483
-- title:
--   The compensating set is a full unit class.
-- statement:
--   **The compensating set is a full unit class.**  Every prime `q` congruent to
--   `N₀·p` modulo the conductor `4∏A` compensates: the semiprime `p·q` has exactly
--   the observed fingerprint.  This is the entire non-analytic content of the
--   no-pruning theorem — a congruence condition modulo a fixed modulus, with no
--   appeal to Dirichlet.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.compensating_class_works(hA : ∀ a ∈ A, a.Prime) {N₀ p q : ℕ}
--       (hN₀ : Odd N₀) (hp : p.Prime) (hpodd : Odd p) (hq : q.Prime)
--       (hpA : ∀ a ∈ A, a ≠ p) (hcong : q ≡ N₀ * p [MOD qrConductor A]) :
--       qrFingerprint A (p * q) = qrFingerprint A N₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageEffective.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageEffective.lean#L42

-- Thm stub generated from Bridges/ResidueLeakageEffective.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
/-
# The compensator lives in a single unit class: effective no-pruning (conjecture C1)

Ninth file of the residue-leakage thread.  `dirichlet_no_pruning` is purely
existential: it invokes Dirichlet's theorem to produce a compensating prime `q`
with `F_A(p·q) = F_A(N₀)`, with no control on the size of `q`.  Conjecture C1 of
`FUTURE_DIRECTIONS.md` asks for an *effective* version.

This file isolates exactly the arithmetic content of that conjecture and
reduces it to a statement about primes in arithmetic progressions:

* `compensating_class_coprime` / `compensating_class_works` — the compensating
  set is a **full unit class modulo the conductor**: *every* prime
  `q ≡ N₀·p (mod 4∏A)` compensates, and `N₀·p` is a unit mod `4∏A`.
  No analytic input at all is used here; this is a congruence statement.
* `effective_no_pruning_of_linnik` — consequently, *any* effective bound `B` for
  the least prime in a coprime residue class modulo `4∏A` is inherited verbatim
  by the compensator.  Linnik's theorem (`B = C·M^L`) therefore turns
  no-pruning into a constructive, polynomial-time defeat of the residue sieve.
  The hypothesis is a genuine (classically true) statement about the modulus
  `4∏A`, supplied as an explicit assumption rather than assumed as an axiom.
* `no_pruning_of_dirichlet_class` — conversely, the qualitative theorem is
  recovered from the same lemma plus infinitude of primes in the class, showing
  that the congruence lemma is the *whole* non-analytic content of no-pruning.
-/


open Bridges.ResidueLeakage

variable {A : List ℕ}

theorem Bridges.ResidueLeakage.compensating_class_works(hA : ∀ a ∈ A, a.Prime) {N₀ p q : ℕ}
    (hN₀ : Odd N₀) (hp : p.Prime) (hpodd : Odd p) (hq : q.Prime)
    (hpA : ∀ a ∈ A, a ≠ p) (hcong : q ≡ N₀ * p [MOD qrConductor A]) :
    qrFingerprint A (p * q) = qrFingerprint A N₀ := by sorry
