-- Prove2me | Definitions.Def_BruhatTits_Utils_RingHom
-- name    : BruhatTits_Utils_RingHom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:40:28.45519+00:00
-- url     : https://prove2.me/theorems/e08c527f-af8b-4eee-bc93-0592bcf23928
-- title:
--   Ring Hom
-- statement:
--   Definitions and structural lemmas for Ring Hom, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
@[simp]
def GL.map {α : Type*} [DecidableEq α] [Fintype α] (g : GL α R) : GL α S where
  val := f.mapMatrix g
  inv := f.mapMatrix g.inv
  val_inv := by rw [← map_mul]; simp
  inv_val := by rw [← map_mul]; simp
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {K : Type*} [CommRing K] (R : Subring K)
instance {α β : Type*} : CoeHead (Matrix α β R) (Matrix α β K) where
  coe g := g.map R.subtype
instance {α : Type*} [DecidableEq α] [Fintype α] : CoeHead (GL α R) (GL α K) where
  coe g := GL.map R.subtype g


