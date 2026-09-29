-- Prove2me | Theorems.Thm_mme_dwz_recursive_target_words_preserve_original_parent_profiles
-- name    : mme_dwz_recursive_target_words_preserve_original_parent_profiles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:27:44.007178+00:00
-- url     : https://prove2.me/theorems/1da5761c-0187-4472-b0c9-e332326f71f2
-- title:
--   Recursive target words preserve inherited parent profiles exactly
-- statement:
--   Let the regions be indexed by $r\in[R]$. Region $r$ has parent grade $P_r\in\mathbb N^3$ with total $8$, $n_r$ parent positions, and admissible left square-child grades $c\in\{0,\ldots,4\}^3$ satisfying $|c|=4$ and $c\le P_r$. The right child's grade is $P_r-c$.
--
--   Fix exact joint counts $m_r(c)$ and a target address $a_r:[n_r]\to\{c\}$ realizing those counts. Let $\iota_r\in\{X,Y,Z\}$ be the inherited profile's retained mode in region $r$. Let $p_r$ have positive integer denominator $D_r$, counts $p_{r,j}$, and scale $s_r$. Assume only the address-data marginal identities
--   $$
--   \sum_{c:c_{\iota_r}=j}m_r(c)=s_rp_{r,j}\qquad(j=0,\ldots,4).
--   $$
--   Every fine word graded by this target address satisfies the original parent coarse grades in each paired position. In the retained mode, its left-child histogram is exactly $s_rp_r$. Thus, for every choice of exact useful-child profiles and every mode $i$, the parent-profile holes among the actual unbroken words are empty:
--   $$
--   \{f\in\mathcal U_i(a):f\text{ violates the inherited parent constraints}\}=\varnothing.
--   $$
--   This part holds at every fine-word length; it uses grading and the target address counts, not typicality.
--
--   At the square-child level, let $x$ be any actual atomic CW-coordinate word whose labels have the required grades. If $i=\iota_r$, $P_{r,i}=Z$, and $n_r=D_rs_r$, its coordinates pack in the literal order
--   $$
--   ((x_{r,t,0,0},x_{r,t,0,1}),(x_{r,t,1,0},x_{r,t,1,1}))
--   $$
--   into a canonical grade-$Z$ fourth-power coordinate word satisfying the original prescribed split profile $p_r$ exactly. The formal conclusion includes this coordinate identity, not merely existence of some word with the same histogram.
--
--   The retained mode may vary by region, so cyclic rotations transport the inherited filter without replacing it by a new Z filter. Zero counts, empty regions, and every $q\ge0$ are allowed. The theorem removes the parent-profile hole term; it does not remove compatibility holes, supply a simultaneous tensor restriction, or prove a component value.
-- source:
--   Derived exact parent-filter preservation from Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Sections 3.5 and 3.9 (leveled partitions and prescribed splitting), Section 7.1 (six-region orientation, target types and child partition). The theorem identifies a deterministic zero-loss parent-profile condition; it is distinct from the probabilistic useful/typical-block comparison in Section 7.2 and Appendix C.

import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_hash_filter
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.CompleteSplit.CWFourth
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_recursive_target_words_preserve_original_parent_profiles
    (q R L : ℕ) (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 8)
    (m : ∀ r, RecursiveThinSplit.Split 4 (parent r) → ℕ)
    (keptMode : Fin R → Fin 3)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (hprofile : ∀ r j,
      (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j},
        m r c.val) = (p r).count j * scale r)
    (a : Address 4 R parent n) (ha : a ∈ RecursiveXHash.target m)
    (positions : Fin L ≃ Position n) :
    let keep : ∀ ell, Fin 3 → (Position n → CompleteWord ell) → Prop := fun _ell i f ↦
      (∀ r t, CWCells.grade (f ⟨r,t,0⟩) + CWCells.grade (f ⟨r,t,1⟩) = parent r i) ∧
      (∀ r, i = keptMode r → ∀ j : Fin 5,
        (Finset.univ.filter (fun t : Fin (n r) ↦
          CWCells.grade (f ⟨r,t,0⟩) = j.val)).card = (p r).count j * scale r)
    (∀ ell i (mu : Cell 4 R parent → CompleteWord ell → ℕ),
      (unbrokenWords htotal i a mu).filter (fun f ↦ ¬ keep ell i f) = ∅) ∧
    ∀ (i : Fin 3) (x : CWCells.WordIndex.{u} q 2 L),
      Graded htotal i a (CWCells.label q 2 L positions x) →
      ∀ (r : Fin R), i = keptMode r →
      ∀ (Z : Fin 9), parent r i = Z.val →
      ∀ hlen : n r = (p r).length (scale r),
      ∃ w : PowIndex (LiftedCoarseCoordinate.{u} q Z) ((p r).length (scale r)),
        prescribedZWord (fun b : LiftedCoarseCoordinate.{u} q Z ↦
          cwSquarePairGrade q b.down.val.1) (p r) (scale r) w ∧
        ∀ t,
          let v := Fin.cast hlen.symm t
          (PowIndex.get _ w t).down.val =
            (((x (finProdFinEquiv (positions.symm ⟨r,v,0⟩, (0 : Fin 2)))).down,
               (x (finProdFinEquiv (positions.symm ⟨r,v,0⟩, (1 : Fin 2)))).down),
              ((x (finProdFinEquiv (positions.symm ⟨r,v,1⟩, (0 : Fin 2)))).down,
               (x (finProdFinEquiv (positions.symm ⟨r,v,1⟩, (1 : Fin 2)))).down)) := by sorry
