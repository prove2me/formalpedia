-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_parity_relabel
-- name    : Couret.InterIA.SingletonNecessity.parity_relabel
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:27.204634+00:00
-- url     : https://prove2.me/theorems/73626779-87f6-4d63-ab86-a92888d5deb2
-- title:
--   Parity-matched doubles admit cross or mixed normal labels
-- statement:
--   Let $G$ be an abelian group, and let $x_0,\ldots,x_5\in G$ be such that $0,x_0,\ldots,x_5$ are pairwise distinct. Put $A=\{0,x_0,x_1,x_2\}$, $B=\{0,x_3,x_4,x_5\}$, $L=[x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2]$, and $R=[x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5]$. Assume that for each $z$, the number of indices $i<3$ with $2x_i=z$ and the number of indices $3\le i<6$ with $2x_i=z$ have the same parity. Then one can choose $y_0,\ldots,y_5$ with $0,y_0,\ldots,y_5$ pairwise distinct and unchanged left and right supports, such that
--
--   $$(2y_0=2y_3,\ 2y_1=2y_4,\ 2y_2=2y_5)\quad\text{or}\quad(2y_0=2y_1,\ 2y_3=2y_4,\ 2y_2=2y_5).$$
--
--   This reduces all parity matchings to two canonical patterns.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ParityRelabel.lean, lines 10–135; source file SHA-256 e38c100083df9eeb8ec0d544ff8ea7bc62af4aac0fcd7a4c8a30c69d9cc7593a; theorem Couret.InterIA.SingletonNecessity.parity_relabel

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_parity_has_pairing
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_reindex
import Theorems.Thm_Couret_InterIA_SingletonNecessity_supportLeft_reindex
import Theorems.Thm_Couret_InterIA_SingletonNecessity_supportRight_reindex
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem parity_relabel (x : Fin 6 → G) (hd : SevenDistinct x)
    (hp : FibreParity (fun i => x i+x i)) :
    ∃ y : Fin 6 → G, SevenDistinct y ∧ supportLeft y=supportLeft x ∧
      supportRight y=supportRight x ∧ (CrossDoubles y ∨ MixedDoubles y) := by sorry


end Couret.InterIA.SingletonNecessity
