-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paired_partner_fixed_source
-- name    : Couret.STROBO2TORS.paired_partner_fixed_source
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:31:12.591179+00:00
-- url     : https://prove2.me/theorems/5ed5130c-a3b2-4273-9673-08d5ee6953ec
-- title:
--   A paired collision is ordinary or reflected ordinary
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Let three-element supports be $S=\{a,b,b+d\}$ and $T=\{u,c,c+e\}$, with $2d=2e=0$, $e\ne0$, $2a\ne2b$, $2u\ne2c$, and $Q_S=Q_T$. Then either $O(S,T)$, or $$3(b-a)\in\{0,d\}\quad\text{and}\quad O(\{a,2b-a,2b-a+d\},T).$$
--
--   The theorem does not separately assume $d\ne0$. The ordinary relation $O(S,T)$ means $T=S+u$ for some $u$ with $2u=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 108–145; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.paired_partner_fixed_source

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem paired_partner_fixed_source (S T : Finset G)
    (a b t c d e : G) (hS : S.card = 3) (hT : T.card = 3)
    (hd : d + d = 0) (he : e + e = 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b) (htc : t + t ≠ c + c)
    (hs : S = {a, b, b + d}) (ht : T = {t, c, c + e})
    (hsq : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    OrdinaryPartner S T ∨
      ((((b - a) + (b - a)) + (b - a) = 0 ∨
         ((b - a) + (b - a)) + (b - a) = d) ∧
        OrdinaryPartner ({a, b + b - a, (b + b - a) + d} : Finset G) T) := by sorry




section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
