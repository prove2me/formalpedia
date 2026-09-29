-- Prove2me | solution 1 for AsymmetricExponent.eulerGap_33_eq_35
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:19:14.903514+00:00
-- url     : https://prove2.me/submissions/fbc99b84-3100-4a08-a3af-54f7c7c7e95a

-- Sol generated from Cryptography/AsymmetricExponent/HintHierarchy.lean
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





open AsymmetricExponent in
theorem solution: eulerGap 3 11 = eulerGap 5 7 := by
  simp [eulerGap]
