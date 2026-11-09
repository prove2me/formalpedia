-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryPartner_inter_two_param
-- name    : Couret.STROBO2TORS.ordinaryPartner_inter_two_param
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:30.599501+00:00
-- url     : https://prove2.me/theorems/efe7986b-9a1e-4700-a63a-e4e669f5a97d
-- title:
--   Parameter form of an ordinary pair with overlap two
-- statement:
--   Let $G$ be an abelian group. Let $S,T$ be finite supports with $|S|=3$, $T=S+u_0$ for some $2u_0=0$, and $|S\cap T|=2$. Then there exist $a,u,b\in G$ with $2u=0$, $u\ne0$, $b\notin\{a,a+u\}$ and
--
--   $$S=\{a,a+u,b\},\qquad T=\{a,a+u,b+u\}.$$
--
--   This parameterizes ordinary delta-two collisions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaTwoCount.lean, lines 74–137; source file SHA-256 cb89a555428b446017e32cc8ccac7e557459a109f1144b64f2304523abb8127d; theorem Couret.STROBO2TORS.ordinaryPartner_inter_two_param

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_inter_translateSupport_add_mem
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem ordinaryPartner_inter_two_param
    (S T : Finset G) (hS : S.card = 3)
    (hOrd : OrdinaryPartner S T) (hI : (S ∩ T).card = 2) :
    ∃ a u b : G, u + u = 0 ∧ u ≠ 0 ∧ b ≠ a ∧ b ≠ a + u ∧
      S = {a, a + u, b} ∧ T = {a, a + u, b + u} := by sorry


variable [Fintype G]











attribute [local instance] Classical.propDecidable






















end Couret.STROBO2TORS
