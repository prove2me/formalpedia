-- Prove2me | Definitions.Def_Couret_SingletonNormalization_99875800f8c3
-- name    : Couret_SingletonNormalization_99875800f8c3
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:20.672087+00:00
-- url     : https://prove2.me/theorems/03b33047-5e63-4b0f-9597-7a9080ae5a28
-- title:
--   Translate a common point to zero
-- statement:
--   For a finite support $A$ and point $p$ in an abelian group, define $$A-p=\{x-p:x\in A\}.$$ This normalization map is applied simultaneously to supports sharing a single point, placing that point at the identity while retaining the relevant collision relationships.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SingletonNormalization.lean; source file SHA-256 b79e3a7dcd27241fd2b42296a8a3585acdf1ea087086ba375ded443d56f96cf2

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def translate (A : Finset G) (p : G) : Finset G := A.image (fun x => x-p)











end Couret.InterIA.SingletonNecessity


