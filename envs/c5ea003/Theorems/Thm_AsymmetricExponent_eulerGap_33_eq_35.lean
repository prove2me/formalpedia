-- Prove2me | Theorems.Thm_AsymmetricExponent_eulerGap_33_eq_35
-- name    : AsymmetricExponent.eulerGap_33_eq_35
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:35.602322+00:00
-- url     : https://prove2.me/theorems/5f184ba2-b180-4202-b1f8-76c46fa305e2
-- title:
--   EulerGap 33 eq 35
-- statement:
--   Formal statement of `AsymmetricExponent.eulerGap_33_eq_35` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AsymmetricExponent.eulerGap_33_eq_35: eulerGap 3 11 = eulerGap 5 7 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/HintHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/HintHierarchy.lean#L81

-- Thm stub generated from Cryptography/AsymmetricExponent/HintHierarchy.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars

/-!
# The hint hierarchy: which cheap quantities actually factor?

`Q(a) = a^(N-1) mod N` costs `O(log N)` (see `PolyTime.lean`) and its CRT
components are asymmetric (see `Core.lean`), yet every multiplicative
consequence of `Q` factors through the single number `g = gcd(p-1, q-1)`
(see `FermatLiars.lean`).  This file contrasts that with a hint that *does*
factor: Euler's totient.

Main results.

* `AsymmetricExponent.factor_from_totient` — from `N = p*q` and `φ(N)` one
  writes down `p` in closed form.  So `φ` is a factoring hint.
* `AsymmetricExponent.liarGroupIsoOfEulerGapEq` — semiprimes with equal Euler
  gap have *isomorphic* Fermat-liar groups.  Everything the Fermat/`Q` surface
  can see is an isomorphism invariant of that group, hence a function of `g`
  alone: it cannot separate two semiprimes with the same `g`.
* `AsymmetricExponent.liarGroup_33_iso_35` — a concrete instance: `33 = 3·11`
  and `35 = 5·7` have isomorphic liar groups although their factors differ.
-/

open AsymmetricExponent

/-! ## Euler's totient *is* a factoring hint -/





/-! ## `Q` cannot separate semiprimes with the same Euler gap -/

theorem AsymmetricExponent.eulerGap_33_eq_35: eulerGap 3 11 = eulerGap 5 7 := by sorry
