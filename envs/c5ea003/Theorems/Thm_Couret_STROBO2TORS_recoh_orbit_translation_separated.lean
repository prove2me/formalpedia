-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_orbit_translation_separated
-- name    : Couret.STROBO2TORS.recoh_orbit_translation_separated
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:18.595455+00:00
-- url     : https://prove2.me/theorems/d94f5175-9320-40f2-a481-98509daed307
-- title:
--   Covariant nonzero probes identify a two-torsion shift
-- statement:
--   Let $G$ be an abelian group, $(\chi_i)_{i\in I}$ complex additive characters, $S$ a finite support and $P_i$ arbitrary support probes satisfying $P_i(S+u)=\chi_i(u)P_i(S)$ for every $i,u$. Assume every $P_i(S)\ne0$, and $2d=0$, $\chi_i(d)=1$ for all i implies $d=0$. If $2u=2v=0$ and $P_i(S+u)=P_i(S+v)$ for every i, then
--
--   $$u=v.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/60f6d03fdb26a2498e9e856b49f93ad590b99409/research/strobo-2tors-2026-10-12/lean/RecohConditionalBank.lean#L18-L52, lines 18–52; source file SHA-256 139a2f5b1511ebbcff70862427a9c94f347105914d4a3f42f054896624ce9efb; theorem Couret.STROBO2TORS.recoh_orbit_translation_separated

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
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

theorem recoh_orbit_translation_separated
    {I : Type*} (bank : I → AddChar G ℂ) (S : Finset G)
    (probe : I → Finset G → ℂ)
    (hcov : ∀ i u, probe i (translateSupport S u) = bank i u * probe i S)
    (hnonzero : ∀ i, probe i S ≠ 0)
    (hsep : ∀ d : G, d + d = 0 →
      (∀ i, bank i d = 1) → d = 0)
    (u v : G) (hu : u + u = 0) (hv : v + v = 0)
    (heq : ∀ i, probe i (translateSupport S u) =
      probe i (translateSupport S v)) : u = v := by sorry







end Couret.STROBO2TORS
