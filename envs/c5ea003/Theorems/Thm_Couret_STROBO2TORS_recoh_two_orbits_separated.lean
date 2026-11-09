-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_orbits_separated
-- name    : Couret.STROBO2TORS.recoh_two_orbits_separated
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:18.323725+00:00
-- url     : https://prove2.me/theorems/8511e68a-a65b-4033-940c-94eef6b07950
-- title:
--   An extra covariant probe distinguishes two matched orbits
-- statement:
--   Let $G$ be an abelian group, $S,T$ finite supports, $(\chi_i)$ a complex character bank and $\beta$ another character. Let probes $P_i$ be covariant under every translation of both S and T with multipliers $\chi_i$, and an extra probe E covariant on both with multiplier β. Assume $P_i(S)=P_i(T)\ne0$ for all i, the bank separates two-torsion, and $E(S)\ne E(T)$. There are no $u,v$ with $2u=2v=0$ satisfying
--
--   $$P_i(S+u)=P_i(T+v)\ (i\in I),\qquad E(S+u)=E(T+v).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/60f6d03fdb26a2498e9e856b49f93ad590b99409/research/strobo-2tors-2026-10-12/lean/RecohConditionalBank.lean#L57-L96, lines 57–96; source file SHA-256 139a2f5b1511ebbcff70862427a9c94f347105914d4a3f42f054896624ce9efb; theorem Couret.STROBO2TORS.recoh_two_orbits_separated

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_orbit_translation_separated
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

/-!
RECOH conditional reconstruction, step 1: orbit separation.
This is an abstract lemma requiring nonvanishing covariant probes and
characters separating two-torsion. No unproved character-existence
assumption is hidden in this theorem.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_two_orbits_separated
    {I : Type*} (bank : I → AddChar G ℂ)
    (beta : AddChar G ℂ) (S T : Finset G)
    (probe : I → Finset G → ℂ) (extra : Finset G → ℂ)
    (hcovS : ∀ i u, probe i (translateSupport S u) = bank i u * probe i S)
    (hcovT : ∀ i u, probe i (translateSupport T u) = bank i u * probe i T)
    (hextraS : ∀ u, extra (translateSupport S u) = beta u * extra S)
    (hextraT : ∀ u, extra (translateSupport T u) = beta u * extra T)
    (hnonzero : ∀ i, probe i S ≠ 0)
    (hsep : ∀ d : G, d + d = 0 →
      (∀ i, bank i d = 1) → d = 0)
    (hbase : ∀ i, probe i S = probe i T)
    (hbeta : extra S ≠ extra T)
    (u v : G) (hu : u + u = 0) (hv : v + v = 0)
    (hmatch : ∀ i, probe i (translateSupport S u) =
      probe i (translateSupport T v))
    (hbetaMatch : extra (translateSupport S u) =
      extra (translateSupport T v)) : False := by sorry



end Couret.STROBO2TORS
