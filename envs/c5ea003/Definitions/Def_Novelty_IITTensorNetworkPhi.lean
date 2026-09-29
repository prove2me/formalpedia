-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkPhi
-- name    : Novelty_IITTensorNetworkPhi
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:51:38.53988+00:00
-- url     : https://prove2.me/theorems/11bae3a3-5755-42f5-885a-ae1de7b290d5
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkPhi
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkPhi`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkPhi.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IntegratedInformation

/-! # Integrated information of a tensor network state

We attach to a quantum state of a chain of `n` sites with local dimension `d`
the integrated information `Φ` of Tononi's theory, formalized through the
catalog's `IntegratedInformation.CausalStructure`: the admissible cuts are the
`n - 1` bipartitions of the chain into a left block and a right block, and the
information destroyed by a cut is the quantum mutual information carried across
that cut by the state.  Thus, *by construction*,

`Φ = min over bipartitions of the quantum mutual information`,

and the substantive content is in the theorems relating `Φ` to the tensor
network data:

* `phi_le_mutualInformation`, `exists_minimal_cut` : `Φ` is the minimum of the
  mutual information over bipartitions;
* `phi_eq_zero_iff_exists_product_cut` : `Φ = 0` exactly when the state
  factorizes (Schmidt rank one) across some cut, i.e. exactly when the state is
  *reducible* in the sense of IIT;
* `phi_le_two_log_of_bondDim` : a cut of bond dimension `χ` caps `Φ` at
  `2 log χ` — an MPS with bond dimension `2` has `Φ ≤ 2 log 2 = log 4`;
* `phi_ghz`, `phi_ghz_saturates_bond_bound` : the GHZ chain state has
  `Φ = 2 log d` where `d` is both its bond dimension
  (`hasBondDim_chainCutMatrix_ghz`) and its Schmidt rank at every cut; for
  `d = 2` this gives `Φ = 2 log 2 = log 4`, twice the logarithm of the Schmidt
  rank `2` (`phi_ghz_qubits`).
-/

open Finset Matrix
open scoped ComplexOrder

namespace IITTensorNetwork

section Chain

variable {n d : ℕ}

/-- Glue a configuration of the first `l` sites and a configuration of the
remaining `n - l` sites into a configuration of the whole chain. -/
def glue (l : ℕ) (hl : l ≤ n) (f : Fin l → Fin d) (g : Fin (n - l) → Fin d) : Fin n → Fin d :=
  fun i => if h : (i : ℕ) < l then f ⟨i, h⟩ else g ⟨(i : ℕ) - l, by have := i.isLt; omega⟩

/-- The restriction of a chain configuration to the first `l` sites. -/
def splitL (l : ℕ) (hl : l ≤ n) (s : Fin n → Fin d) : Fin l → Fin d :=
  fun i => s ⟨i, by have := i.isLt; omega⟩

/-- The restriction of a chain configuration to the last `n - l` sites. -/
def splitR (l : ℕ) (hl : l ≤ n) (s : Fin n → Fin d) : Fin (n - l) → Fin d :=
  fun j => s ⟨l + j, by have := j.isLt; omega⟩

lemma splitL_glue (l : ℕ) (hl : l ≤ n) (f : Fin l → Fin d) (g : Fin (n - l) → Fin d) :
    splitL l hl (glue l hl f g) = f := by
  funext i
  have h : ((⟨i, by have := i.isLt; omega⟩ : Fin n) : ℕ) < l := i.isLt
  simp [splitL, glue, h]

lemma splitR_glue (l : ℕ) (hl : l ≤ n) (f : Fin l → Fin d) (g : Fin (n - l) → Fin d) :
    splitR l hl (glue l hl f g) = g := by
  funext j
  have h : ¬ (((⟨l + j, by have := j.isLt; omega⟩ : Fin n) : ℕ) < l) := by
    simp only []
    omega
  simp only [splitR, glue, dif_neg h]
  congr 1
  apply Fin.ext
  simp

lemma glue_splitL_splitR (l : ℕ) (hl : l ≤ n) (s : Fin n → Fin d) :
    glue l hl (splitL l hl s) (splitR l hl s) = s := by
  funext i
  by_cases h : (i : ℕ) < l
  · simp [glue, splitL, h]
  · simp only [glue, dif_neg h, splitR]
    congr 1
    apply Fin.ext
    simp only []
    omega

/-- Splitting a chain configuration at position `l` is a bijection. -/
def chainEquiv (l : ℕ) (hl : l ≤ n) :
    (Fin n → Fin d) ≃ (Fin l → Fin d) × (Fin (n - l) → Fin d) where
  toFun s := (splitL l hl s, splitR l hl s)
  invFun p := glue l hl p.1 p.2
  left_inv s := glue_splitL_splitR l hl s
  right_inv p := by
    ext1
    · exact splitL_glue l hl p.1 p.2
    · exact splitR_glue l hl p.1 p.2

/-- The coefficient matrix of a chain state across the cut at position `l`. -/
noncomputable def chainCutMatrix (psi : (Fin n → Fin d) → ℂ) (l : ℕ) (hl : l ≤ n) :
    Matrix (Fin l → Fin d) (Fin (n - l) → Fin d) ℂ :=
  Matrix.of fun f g => psi (glue l hl f g)

/-- A normalized chain state has normalized cut matrices. -/
theorem normalized_chainCutMatrix {psi : (Fin n → Fin d) → ℂ}
    (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (l : ℕ) (hl : l ≤ n) :
    Normalized (chainCutMatrix psi l hl) := by
  have hsum : ∑ p : (Fin l → Fin d) × (Fin (n - l) → Fin d),
      ‖psi ((chainEquiv l hl).symm p)‖ ^ 2 = ∑ s, ‖psi s‖ ^ 2 :=
    Equiv.sum_comp (chainEquiv l hl).symm (fun s => ‖psi s‖ ^ 2)
  rw [Fintype.sum_prod_type, hpsi] at hsum
  exact hsum

/-- The IIT causal structure of a chain state: the admissible cuts are the
`n - 1` bipartitions into a left block and a right block, and the information
lost at a cut is the quantum mutual information across it. -/
noncomputable def chainCausalStructure {psi : (Fin n → Fin d) → ℂ}
    (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) : IntegratedInformation.CausalStructure where
  Cut := Fin (n - 1)
  cutNonempty := ⟨⟨0, by omega⟩⟩
  loss p := mutualInformation (chainCutMatrix psi ((p : ℕ) + 1) (by have := p.isLt; omega))
  loss_nonneg p :=
    mutualInformation_nonneg (normalized_chainCutMatrix hpsi ((p : ℕ) + 1) (by
      have := p.isLt; omega))

/-- The integrated information of a chain state: the minimum, over all
bipartitions of the chain, of the quantum mutual information across the cut. -/
noncomputable def Phi {psi : (Fin n → Fin d) → ℂ} (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) :
    ℝ :=
  IntegratedInformation.Phi (chainCausalStructure hpsi hn)

variable {psi : (Fin n → Fin d) → ℂ}









end Chain

section GHZ

variable {n d : ℕ}

/-- The GHZ state of a chain of `n` sites with local dimension `d`: an equal
superposition of the `d` constant configurations. -/
noncomputable def ghzState (n d : ℕ) : (Fin n → Fin d) → ℂ :=
  fun s => if ∀ i j, s i = s j then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0

/-- The constant configuration of a block of `k` sites with common value `x`. -/
def constCfg (k d : ℕ) : Fin d → (Fin k → Fin d) := fun x _ => x












end GHZ

end IITTensorNetwork


