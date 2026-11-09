-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_common_kernel_translation_collision
-- name    : Couret.STROBO2TORS.recoh_common_kernel_translation_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:35.075195+00:00
-- url     : https://prove2.me/theorems/90a818d4-e413-4220-9b31-5bf23389bb06
-- title:
--   A half-turn invisible to every probe preserves the observation
-- statement:
--   Let $G$ be an abelian group, $R$ a commutative ring, $S=\{a,b,c\}$ have size three, and $d\ne0$ satisfy $2d=0$. Let $L$ be a list of functions $f:G\to R$ satisfying $f(x+y)=f(x)f(y)$ and $f(d)=1$. Then
--
--   $$S\ne S+d,\qquad R_S=R_{S+d},\qquad\sum_{s\in S}f(s)=\sum_{s\in S+d}f(s)\quad(f\in L).$$
--
--   This is a collision for the entire supplied bank, which may be empty.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCharacterMasks.lean, lines 94–127; source file SHA-256 2f48c1baa26825432269452ec7f65dbaede084f1d2dd01b4d0f22f7d0b963d87; theorem Couret.STROBO2TORS.recoh_common_kernel_translation_collision

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
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

theorem recoh_common_kernel_translation_collision
    {R : Type*} [CommRing R]
    (a b c d : G)
    (hcard : ({a, b, c} : Finset G).card = 3)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (bank : List (G → R))
    (hadd : ∀ chi ∈ bank, ∀ x y : G, chi (x + y) = chi x * chi y)
    (htrivial : ∀ chi ∈ bank, chi d = 1) :
    (({a, b, c} : Finset G) ≠ {a + d, b + d, c + d}) ∧
      (∀ z : G, orderedSquare ({a, b, c} : Finset G) z =
        orderedSquare ({a + d, b + d, c + d} : Finset G) z) ∧
      (∀ chi ∈ bank, recohTripleProbe chi a b c =
        recohTripleProbe chi (a + d) (b + d) (c + d)) := by sorry


end Couret.STROBO2TORS
