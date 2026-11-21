-- Prove2me | Definitions.Def_Kourovka_Paths
-- name    : Kourovka_Paths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:28:51.49387+00:00
-- url     : https://prove2.me/theorems/f0d6bd56-ad2c-4efb-9d64-deb1ebf60ab4
-- title:
--   Paths
-- statement:
--   Definitions and structural lemmas for Paths, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Paths.lean

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
set_option autoImplicit true
namespace Kourovka
namespace ProductPaths
variable {A B : Type*} [Group A] [Group B]
def axis : Bool → (A × B →* A × B)
  | false => (MonoidHom.inl A B).comp (MonoidHom.fst A B)
  | true => (MonoidHom.inr A B).comp (MonoidHom.snd A B)
def path (f : A × B →* A × B) : List Bool → (A × B →* A × B)
  | [] => MonoidHom.id _
  | i :: is => (axis i).comp (f.comp (path f is))
def Nonabelian (f : A × B →* A × B) (w : List Bool) : Prop :=
  ∃ x y, ¬ Commute (path f w x) (path f w y)
end ProductPaths
end Kourovka


