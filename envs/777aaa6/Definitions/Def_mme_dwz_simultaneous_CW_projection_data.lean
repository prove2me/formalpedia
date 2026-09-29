-- Prove2me | Definitions.Def_mme_dwz_simultaneous_CW_projection_data
-- name    : mme_dwz_simultaneous_CW_projection_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T09:43:10.707832+00:00
-- url     : https://prove2.me/theorems/747291b4-9f59-47c2-bd70-afb075b553bc
-- title:
--   Coordinate filters for simultaneous boundary-owned CW extraction
-- statement:
--   Fix a field $K$, nonnegative integers $q,\ell,N,k$, a set $C$ of component labels, and maps assigning a component $c_j(t)\in C$ to each selected owner $j<k$ and position $t<N$. A shape map assigns three nonnegative coarse grades to every component. Write $d=2^{\ell-1}$.
--
--   This interface defines the actual source tensor
--   $$
--   T=\mathrm{CW}_q^{\otimes Nd}
--   $$
--   with its canonical word basis. Each basis word has a fine-grade label in $\{0,1,2\}^{N\times d}$. It also defines coarse addresses, their marginal histograms, coordinatewise mixing, and retention under one state of the public asymmetric hash.
--
--   For a tag map $\theta:\{0,1,2\}^d\to W$ and prescribed integer histograms $\mu_i(c,w)$, a fine Z-word is boundary-compatible with owner $j$ when its coarse Z-grade agrees with that owner and its tag counts equal $\mu_2(c,w)$ on every component whose X- or Y-grade is zero.
--
--   The allowed-coordinate predicates impose the owner's coarse grade in every mode. X tag histograms are prescribed only on zero-Y components; Y tag histograms only on zero-X components. Z tag histograms are prescribed on every component, and a Z-word is retained only if it is boundary-compatible with no owner other than its designated owner. Thus the eventual projected summand is determined by literal coordinate predicates, rather than by an assumed tensor restriction.
--
--   For $\ell=3$, the additional tag construction records the sum of the first two atomic grades, an element of $\{0,1,2,3,4\}$. On a fixed coarse fiber this is the left-square label of a fourth-power block. The interface contains only data and constructions; it asserts no positive block count or asymptotic estimate.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS1, Section 6.1, Definition 6.1, Claim 6.2, Definition 6.3, and the direct-sum assertion immediately following Additional Zeroing-Out Step 2. This is an explicit finite, single-region CW-source realization lemma with arbitrary reflection-compatible tags, not the full asymptotic value theorem.

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Data.Fin.Rev

open BigOperators
open MME Module MME.TensorObj MME.CompleteSplit MME.DWZStep1Support

universe u v w

set_option autoImplicit false

namespace MME.DWZSimultaneous

abbrev CoarseAddress (N : ℕ) := Fin 3 → Fin N → ℕ

def Supported {N : ℕ} (level : ℕ) (a : CoarseAddress N) : Prop :=
  ∀ t, a 0 t + a 1 t + a 2 t = level

def SameMarginal {N : ℕ} (marginal : Fin 3 → ℕ → ℕ) (a : CoarseAddress N) : Prop :=
  ∀ i g, Fintype.card {t : Fin N // a i t = g} = marginal i g

def owner {C : Type v} {N k : ℕ}
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (j : Fin k) : CoarseAddress N := fun i t ↦ shape (component j t) i

def mix {N : ℕ} (x y z : CoarseAddress N) : CoarseAddress N
  | 0 => x 0
  | 1 => y 1
  | 2 => z 2

def fieldWord {N H p : ℕ} (reindex : Fin (H + 1) ≃ Fin N)
    (word : Fin N → ℕ) : Fin (H + 1) → ZMod p :=
  fun t ↦ (word (reindex t) : ZMod p)

def hash {N H p : ℕ} (level : ℕ) (reindex : Fin (H + 1) ≃ Fin N)
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (i : Fin 3) (word : Fin N → ℕ) : ZMod p :=
  Fin.cases
    (dwzAsymmetricHashX (dwzAsymmetricHashStateOfAffine state) (fieldWord reindex word))
    (fun i' ↦ Fin.cases
      (dwzAsymmetricHashY (dwzAsymmetricHashStateOfAffine state) (fieldWord reindex word))
      (fun _ ↦ dwzAsymmetricHashZ (level : ZMod p)
        (dwzAsymmetricHashStateOfAffine state) (fieldWord reindex word)) i') i

def Retained {N H p : ℕ} (level : ℕ) (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (a : CoarseAddress N) : Prop :=
  ∃ s ∈ S, ∀ i, hash level reindex state i (a i) = (s : ZMod p)

abbrev FineWord (ell N : ℕ) := Fin N → CompleteWord ell

def reverseWord {ell : ℕ} (v : CompleteWord ell) : CompleteWord ell :=
  fun r ↦ Fin.rev (v r)

/-- The literal left-square grade of a fourth-power complete word. -/
def fourthLeftTag (v : CompleteWord 3) : Fin 5 :=
  ⟨(v 0).val + (v 1).val, by
    have h0 := (v 0).isLt
    have h1 := (v 1).isLt
    omega⟩

def Graded {C : Type v} {ell N k : ℕ}
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (j : Fin k) (i : Fin 3) (f : FineWord ell N) : Prop :=
  ∀ t, ∑ r, (f t r).val = shape (component j t) i

def Profile {C : Type v} {W : Type w} [DecidableEq C] [DecidableEq W]
    {ell N k : ℕ} (component : Fin k → Fin N → C)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (j : Fin k) (i : Fin 3) (f : FineWord ell N) : Prop :=
  ∀ c w, Fintype.card {t : Fin N // component j t = c ∧ tag (f t) = w} = mu i c w

def ZCompatible {C : Type v} {W : Type w} [DecidableEq C] [DecidableEq W]
    {ell N k : ℕ} (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (j : Fin k) (f : FineWord ell N) : Prop :=
  Graded component shape j 2 f ∧
    ∀ c, shape c 0 = 0 ∨ shape c 1 = 0 → ∀ w,
      Fintype.card {t : Fin N // component j t = c ∧ tag (f t) = w} = mu 2 c w

def Allowed {C : Type v} {W : Type w} [DecidableEq C] [DecidableEq W]
    {ell N k : ℕ} (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (j : Fin k) (i : Fin 3) (f : FineWord ell N) : Prop :=
  Graded component shape j i f ∧
    (i = 0 → ∀ c, shape c 1 = 0 → ∀ w,
      Fintype.card {t : Fin N // component j t = c ∧ tag (f t) = w} = mu 0 c w) ∧
    (i = 1 → ∀ c, shape c 0 = 0 → ∀ w,
      Fintype.card {t : Fin N // component j t = c ∧ tag (f t) = w} = mu 1 c w) ∧
    (i = 2 → Profile component tag mu j 2 f) ∧
    (i = 2 → ∀ j', ZCompatible component shape tag mu j' f → j' = j)

abbrev WordIndex (q ell N : ℕ) := Fin (N * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2))

noncomputable def source (K : Type u) [Field K] (q ell N : ℕ) : TensorObj K 3 :=
  (CWObj K q).kronPow (N * 2 ^ (ell - 1))

noncomputable def basis (K : Type u) [Field K] (q ell N : ℕ) (i : Fin 3) :
    Basis (WordIndex.{u} q ell N) K ((source K q ell N).V i) :=
  kronPowModeWordBasis (CWObj K q) i
    ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 2 ^ (ell - 1))

def label (q ell N : ℕ) (w : WordIndex.{u} q ell N) : FineWord ell N :=
  fun t r ↦ cwSquareCoordGrade q (w (finProdFinEquiv (t, r))).down

end MME.DWZSimultaneous


