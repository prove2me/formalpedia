-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_count_cancellation
-- name    : Couret.InterIA.SingletonNecessity.cross_count_cancellation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:15.376334+00:00
-- url     : https://prove2.me/theorems/6fbd09db-36a2-4702-87a5-73adae1ae89a
-- title:
--   Cross-matched doubles cancel from a singleton collision
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $G$ be an abelian group, and let $x_0,\ldots,x_5\in G$ be such that $0,x_0,\ldots,x_5$ are pairwise distinct. Put $A=\{0,x_0,x_1,x_2\}$, $B=\{0,x_3,x_4,x_5\}$, $L=[x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2]$, and $R=[x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5]$. If $2x_0=2x_3$, $2x_1=2x_4$, $2x_2=2x_5$, and $R_A=R_B$, then
--
--   $$L\text{ and }R\text{ are permutations of one another}.$$
--
--   The conclusion preserves multiplicities in the six off-diagonal sum terms.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/CountCancellation.lean, lines 8–18; source file SHA-256 a9c6879b38b272efd97ab8636f1963a931fe668d255d7f044d96fb16a8dc1e89; theorem Couret.InterIA.SingletonNecessity.cross_count_cancellation

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportLeft
import Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportRight
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem cross_count_cancellation (x : Fin 6 → G) (hd : SevenDistinct x)
    (hx : CrossDoubles x)
    (hs : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z) :
    (sumTermsLeft x).Perm (sumTermsRight x) := by sorry




end Couret.InterIA.SingletonNecessity
