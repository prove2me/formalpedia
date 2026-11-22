-- Prove2me | solution 1 for BruhatTits.eq_dist_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:52:49.302525+00:00
-- url     : https://prove2.me/submissions/0d44c34e-bd0b-43b3-90a7-3b7fd6c52914

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_signature_antitone
import Theorems.Thm_BruhatTits_signatureBasisTarget_eq
import Theorems.Thm_BruhatTits_eq_signature_iff
import Theorems.Thm_BruhatTits_signature_diff_eq_dist

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (f : Fin 2 → ℤ),
      Irreducible ϖ ∧
        Antitone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 0 - f 1 = n := by
  constructor
  · rintro rfl
    use signatureϖ M L
    use signatureBasisSource M L
    use signatureBasisTarget M L
    use signature M L
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact signatureϖ_irreducible M L
    · exact signature_antitone M L
    · exact signatureBasisTarget_eq M L
    · exact signature_diff_eq_dist M L
  · intro ⟨ϖ, bM, bL, f, hϖ, hf, hi, hn⟩
    have : signature M L = f := by
      apply (eq_signature_iff M L f hf).mpr
      use ϖ, bM, bL
    subst this
    rw [signature_diff_eq_dist M L] at hn
    exact Int.ofNat_inj.mp hn
end BruhatTits
