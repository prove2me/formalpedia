-- Prove2me | solution 1 for BruhatTits.eq_signature_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:50:09.334123+00:00
-- url     : https://prove2.me/submissions/d4d923df-7104-4de6-aa4e-f5b2fcde895c

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_signature_unique
import Theorems.Thm_BruhatTits_signature_antitone
import Theorems.Thm_BruhatTits_signatureBasisTarget_eq

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R)
    (f : Fin 2 → ℤ) (hf : Antitone f) :
    signature M L = f ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      Irreducible ϖ ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by
  constructor
  · rintro rfl
    use signatureϖ M L
    use signatureBasisSource M L
    use signatureBasisTarget M L
    exact ⟨signatureϖ_irreducible M L, signatureBasisTarget_eq M L⟩
  · intro ⟨ϖ, bM, bL, hϖ, h⟩
    exact signature_unique (signatureϖ_irreducible M L) hϖ (signature_antitone M L) hf
      (signatureBasisTarget_eq M L)
      h
end BruhatTits
