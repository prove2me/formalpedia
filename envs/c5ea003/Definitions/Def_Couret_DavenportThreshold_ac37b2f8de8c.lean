-- Prove2me | Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
-- name    : Couret_DavenportThreshold_ac37b2f8de8c
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:56.324193+00:00
-- url     : https://prove2.me/theorems/e2aa226b-42cb-4cda-927a-591e516ee25f
-- title:
--   Davenport threshold for the modulo-30 unit group
-- statement:
--   For $n\in\mathbb N$, the Davenport-bound predicate says that every word of length at least $n$ in the eight unit residues modulo 30 has a nonempty selected product equal to the identity code $(0,0)$. The bundle also specifies the four-letter witness word $((0,1),(0,1),(0,1),(1,0))$.
--
--   This packages the threshold property and a concrete candidate witness for sharpness; the predicate itself does not assert the bound for any particular $n$.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/DavenportThreshold.lean; source file SHA-256 c800425f72bd7cac263232227e182bea9d8881d436ee30021d29b43628c45e05

import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
namespace Couret
namespace S5



def DavenportBound (n : Nat) : Prop :=
  ∀ w : Word Code30, n ≤ length w → selectedSupport w (0,0)



def zeroFreeFour : Word Code30 :=
  .snoc (.snoc (.snoc (.snoc .empty (0,1)) (0,1)) (0,1)) (1,0)























end S5
end Couret


