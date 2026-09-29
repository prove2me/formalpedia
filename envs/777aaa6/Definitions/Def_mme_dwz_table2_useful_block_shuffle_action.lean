-- Prove2me | Definitions.Def_mme_dwz_table2_useful_block_shuffle_action
-- name    : mme_dwz_table2_useful_block_shuffle_action
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T07:41:14.325429+00:00
-- url     : https://prove2.me/theorems/42e45bed-14dc-460b-a217-e7d87395cd08
-- title:
--   DWZ Table-2 useful-block shuffling group and action
-- statement:
--   Fix an outer Table-2 component word $I:P\to\{0,\ldots,14\}$. Its shuffling group is the subgroup $$G_I=\{\phi\in S_P:I_{\phi(t)}=I_t\text{ for every }t\in P\}\cong\prod_s S_{\{t:I_t=s\}}.$$ Thus it is exactly the product of the symmetric groups on the position pairs belonging to each component. It acts on available small Z-blocks by inverse reindexing, $$(\phi\cdot z)_t=z_{\phi^{-1}(t)}.$$ The action preserves the pointwise coarse Z grade and every prescribed componentwise split histogram, and hence is a well-defined action on `UsefulBlock m I`. This is the Table-2 specialization of Definition 5.7 and the preservation assertion of Claim 5.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.3--5.7 and Claim 5.8, PDF pp. 48--49 / printed pp. 47--48.

import Definitions.Def_mme_dwz_table2_useful_block
import Mathlib.Data.Fintype.Perm

/-!
# The Table-2 useful-block shuffling action

For a fixed outer component word, DWZ Definition 5.7 independently permutes
the position pairs belonging to each component.  The subgroup below is this
direct product of symmetric groups, represented as the permutations which
preserve the outer component label pointwise.
-/

set_option autoImplicit false

namespace MME.DWZTable2StandardForm

universe u

/-- Definition 5.7's product of symmetric groups on the component-position
fibers of a fixed Table-2 outer word. -/
def UsefulBlockShuffleGroup
    {Position : Type u} (outer : Position → Fin 15) :
    Subgroup (Equiv.Perm Position) where
  carrier := {e | ∀ t, outer (e t) = outer t}
  one_mem' t := rfl
  mul_mem' := by
    intro e f he hf t
    change outer (e (f t)) = outer t
    rw [he, hf]
  inv_mem' := by
    intro e he t
    have h := he (e.symm t)
    simpa using h.symm

noncomputable instance usefulBlockShuffleGroupFintype
    {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    Fintype (UsefulBlockShuffleGroup outer) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance usefulBlockShuffleGroupDecidableEq
    {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    DecidableEq (UsefulBlockShuffleGroup outer) :=
  Classical.decEq _

/-- Reindex a useful block by a component-fiber-preserving position
permutation.  The inverse is used so these reindexings form a left action. -/
def shuffleUsefulBlock
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15)
    (g : UsefulBlockShuffleGroup outer)
    (small : UsefulBlock m outer) : UsefulBlock m outer := by
  refine ⟨fun t ↦ small.1 (g.1.symm t), ?_, ?_⟩
  · intro t
    calc
      MME.DWZTable2Counts.coarseOf (small.1 (g.1.symm t)) =
          MME.DWZSquare.shapeZ (outer (g.1.symm t)) :=
        small.2.1 (g.1.symm t)
      _ = MME.DWZSquare.shapeZ (outer t) := by
        have h := g.2 (g.1.symm t)
        simpa using congrArg MME.DWZSquare.shapeZ h.symm
  · intro s a
    classical
    let e :
        {t : Position //
          outer t = s ∧ (small.1 (g.1.symm t)).1 = a} ≃
        {t : Position // outer t = s ∧ (small.1 t).1 = a} :=
      Equiv.subtypeEquiv g.1.symm (fun t ↦ by
        have h := g.2 (g.1.symm t)
        have hout : outer (g.1.symm t) = outer t := by
          simpa using h.symm
        rw [hout])
    rw [Fintype.card_congr e]
    exact small.2.2 s a

instance usefulBlockShuffleSMul
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    SMul (UsefulBlockShuffleGroup outer) (UsefulBlock m outer) where
  smul := shuffleUsefulBlock m outer

instance usefulBlockShuffleMulAction
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    MulAction (UsefulBlockShuffleGroup outer) (UsefulBlock m outer) where
  one_smul small := by
    apply Subtype.ext
    funext t
    rfl
  mul_smul g h small := by
    apply Subtype.ext
    funext t
    rfl

end MME.DWZTable2StandardForm


