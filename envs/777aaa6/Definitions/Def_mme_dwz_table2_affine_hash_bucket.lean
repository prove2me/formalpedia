-- Prove2me | Definitions.Def_mme_dwz_table2_affine_hash_bucket
-- name    : mme_dwz_table2_affine_hash_bucket
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T12:37:23.064681+00:00
-- url     : https://prove2.me/theorems/78d8622c-d7c3-4a14-b81a-2232ce915ffc
-- title:
--   The canonical Table-2 affine hash bucket
-- statement:
--   The canonical first-zeroing bucket for Table-2 component words. A word belongs exactly when it lies in the ambient family and its asymmetric X, Y, and Z hashes all lie in the cast progression-free label set. The module also exposes the three coarse component words cast into the hash field. This preserves the semantic hash data that Claim 6.8 needs after the first retention argument.
-- source:
--   Ran Duan, Hongxun, Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric hashing in Section 3.10 and Algorithm 2 / Additional Zeroing-Out Step 1, PDF pp. 25-27 and 52-54; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false
set_option warningAsError true

namespace MME

/-- The coarse X word of a Table-2 component word, cast into the hash field. -/
def dwzTable2CastX {p N : ℕ}
    (w : Fin (N + 1) → Fin 15) : Fin (N + 1) → ZMod p := fun t ↦
  (DWZSquare.shapeX (w t)).val

/-- The coarse Y word of a Table-2 component word, cast into the hash field. -/
def dwzTable2CastY {p N : ℕ}
    (w : Fin (N + 1) → Fin 15) : Fin (N + 1) → ZMod p := fun t ↦
  (DWZSquare.shapeY (w t)).val

/-- The coarse Z word of a Table-2 component word, cast into the hash field. -/
def dwzTable2CastZ {p N : ℕ}
    (w : Fin (N + 1) → Fin 15) : Fin (N + 1) → ZMod p := fun t ↦
  (DWZSquare.shapeZ (w t)).val

/-- The literal affine-hash bucket used in the first DWZ zeroing step.

A component word is retained precisely when all three asymmetric hashes lie
in the cast AP-free label set.  Keeping this bucket public prevents the
first-hash retention theorem from erasing the semantic information later
needed by Claim 6.8. -/
noncomputable def dwzTable2AffineHashBucket {p N : ℕ}
    (S : Finset ℕ) (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    Finset (Fin (N + 1) → Fin 15) := by
  classical
  let castS : Finset (ZMod p) :=
    S.image (fun a : ℕ ↦ (a : ZMod p))
  let ω := dwzAsymmetricHashStateOfAffine q
  exact A.filter (fun w ↦
    dwzAsymmetricHashX ω (dwzTable2CastX w) ∈ castS ∧
      dwzAsymmetricHashY ω (dwzTable2CastY w) ∈ castS ∧
      dwzAsymmetricHashZ (4 : ZMod p) ω (dwzTable2CastZ w) ∈ castS)

end MME


