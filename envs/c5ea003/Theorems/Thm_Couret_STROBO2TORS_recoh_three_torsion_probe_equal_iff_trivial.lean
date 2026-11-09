-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_three_torsion_probe_equal_iff_trivial
-- name    : Couret.STROBO2TORS.recoh_three_torsion_probe_equal_iff_trivial
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:37.133764+00:00
-- url     : https://prove2.me/theorems/7a18d57e-4d3b-4bea-aee7-e877d2c287d4
-- title:
--   A normalized multiplicative probe agrees on opposite three-torsion points only trivially
-- statement:
--   Let $G$ be an abelian group, $R$ a commutative ring, and $f:G\to R$ satisfy $f(x+y)=f(x)f(y)$ and $f(0)=1$. If $3v=0$, then
--
--   $$f(v)=f(-v)\iff f(v)=1.$$
--
--   No domain or characteristic hypothesis is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCharacterMasks.lean, lines 41–80; source file SHA-256 2f48c1baa26825432269452ec7f65dbaede084f1d2dd01b4d0f22f7d0b963d87; theorem Couret.STROBO2TORS.recoh_three_torsion_probe_equal_iff_trivial

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: character masks and genuine translation witnesses.
A dependency of the prospective universal bank bound B(G)=r+s.
No Fourier character-existence or full rank theorem is asserted here.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_three_torsion_probe_equal_iff_trivial
    {R : Type*} [CommRing R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (hzero : chi 0 = 1)
    (v : G) (hv3 : (v + v) + v = 0) :
    (chi v = chi (-v)) ↔ chi v = 1 := by sorry






end Couret.STROBO2TORS
