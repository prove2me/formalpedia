-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportLeft
-- name    : Couret.InterIA.SingletonNecessity.square_supportLeft
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:06:27.598828+00:00
-- url     : https://prove2.me/theorems/b1ec33c4-ded1-4738-befc-7f150b5e2cc3
-- title:
--   Ordered-square expansion of a labeled four-support
-- statement:
--   Let $G$ be an abelian group. Let $0,x_0,\ldots,x_5$ be pairwise distinct and $S=\{0,x_0,x_1,x_2\}$. For $z\in G$, let $Q_S(z)$ count ordered pairs from $S$ summing to $z$, and let $N_L(z)$ count occurrences of $z$ in a list $L$. Then
--
--   $$Q_S(z)=[z=0]+N_{(2x_0,2x_1,2x_2)}(z)+2N_{(x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2)}(z).$$
--
--   This separates diagonal and doubled off-diagonal multiplicities.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SquareExpansion.lean, lines 56–65; source file SHA-256 9bb0068b4b8d7143f97d46947e4be4105b05b8c1d63e1cf936d8c33c351a30cc; theorem Couret.InterIA.SingletonNecessity.square_supportLeft

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem square_supportLeft (x : Fin 6 → G) (hd : SevenDistinct x) (z : G) :
    orderedSquare (supportLeft x) z =
      (if 0=z then 1 else 0) + [x 0+x 0,x 1+x 1,x 2+x 2].count z +
      2 * (sumTermsLeft x).count z := by sorry






end Couret.InterIA.SingletonNecessity
